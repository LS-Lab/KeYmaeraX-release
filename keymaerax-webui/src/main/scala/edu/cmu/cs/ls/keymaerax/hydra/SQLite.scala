/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.hydra

import java.sql.SQLException

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.core.{Formula, Provable, Sequent}
import edu.cmu.cs.ls.keymaerax.hydra.ExecutionStepStatus.ExecutionStepStatus

//import Tables.TacticonproofRow
import edu.cmu.cs.ls.keymaerax.api.KeYmaeraInterface

import scala.slick.driver.SQLiteDriver.simple._
import scala.slick.lifted.{ProvenShape, ForeignKeyQuery}
import edu.cmu.cs.ls.keymaerax.api.KeYmaeraInterface.PositionTacticAutomation

/**
 * Created by nfulton on 4/10/15.
 */
object SQLite extends DBAbstraction {

  import Tables._

  val dblocation = DBAbstractionObj.dblocation

  val sqldb = Database.forURL("jdbc:sqlite:" + dblocation, driver= "org.sqlite.JDBC")


  if(!new java.io.File(dblocation).exists()) {
    this.cleanup()
  }

//@TODO
  // Configuration
  override def getAllConfigurations: Set[ConfigurationPOJO] =
    sqldb.withSession(implicit session => {
      Config.list.filter(_.configname.isDefined).map(_.configname.get).map(getConfiguration(_)).toSet
    })

  override def createConfiguration(configName: String): Boolean =
    sqldb.withSession(implicit session => {
      //This is unnecessary?
      true
    })

  private def blankOk(x : Option[String]):String = x match {
    case Some(y) => y
    case None    => ""
  }

  override def getModelList(userId: String): List[ModelPOJO] = {
    sqldb.withSession(implicit session => {
      Models.filter(_.userid === userId).list.map(element => new ModelPOJO(element.modelid.get, element.userid.get, element.name.get,
        blankOk(element.date), blankOk(element.filecontents),
        blankOk(element.description), blankOk(element.publink), blankOk(element.title), element.tactic))
    })
  }

  override def createUser(username: String, password: String): Unit =
    sqldb.withSession(implicit session => {
      Users.map(u => (u.email.get, u.password.get))
        .insert((username, password))
    })


  private def idgen() : String = java.util.UUID.randomUUID().toString()


  /**
   * Poorly names -- either update the config, or else insert an existing key.
   * But in Mongo it was just update, because of the nested documents thing.
   * @param config
   */
  override def updateConfiguration(config: ConfigurationPOJO): Unit =
    sqldb.withSession(implicit session => {
        config.config.map(kvp => {
          val key = kvp._1
          val value = kvp._2
          val configExists = Config.filter(c => c.configname===config.name && c.key===key).list.length != 0

          if(configExists) {
            val q = for {l <- Config if (l.configname === config.name && l.key === key)} yield l.value
            q.update(Some(value))
          }
          else {
            Config.map(c => (c.configid.get, c.configname.get, c.key.get, c.value.get))
              .insert((idgen, config.name, key, value))
          }
        })
    })

  //Proofs and Proof Nodes
  override def getProofInfo(proofId: String): ProofPOJO =
    sqldb.withSession(implicit session => {
      val stepCount = getProofSteps(proofId).size
      val list = Proofs.filter(_.proofid === proofId)
            .list
            .map(p => new ProofPOJO(p.proofid.get, p.modelid.get, blankOk(p.name), blankOk(p.description),
                                    blankOk(p.date), stepCount, p.closed.getOrElse(0) == 1))
      if(list.length > 1) throw new Exception()
      else if(list.length == 0) throw new Exception()
      else list.head
    })

  // Users
  override def userExists(username: String): Boolean =
    sqldb.withSession(implicit session => {
      Users.filter(_.email === username).list.length != 0
    })


  override def getProofsForUser(userId: String): List[(ProofPOJO, String)] =
    sqldb.withSession(implicit session => {
      val models = getModelList(userId)

      models.map(model => {
        val modelName = model.name
        val proofs = getProofsForModel(model.modelId)
        proofs.map((_, modelName))
      }).flatten
    })

  override def checkPassword(username: String, password: String): Boolean =
    sqldb.withSession(implicit session => {
      Users.filter(_.email === username).filter(_.password === password).list.length != 0
    })

  override def updateProofInfo(proof: ProofPOJO): Unit =
    sqldb.withSession(implicit session => {
      Proofs.filter(_.proofid === proof.proofId).update(proofPojoToRow(proof))
    })

  override def updateProofName(proofId : String, newName : String): Unit = {
    sqldb.withSession(implicit session => {
      Proofs.filter(_.proofid === proofId).map(_.name).update(Some(newName))
    })
  }

  //@todo actually these sorts of methods are rather dangerous because any schema change could mess this up.
  private def proofPojoToRow(p : ProofPOJO) : ProofsRow = new ProofsRow(Some(p.proofId), Some(p.modelId), Some(p.name), Some(p.description), Some(p.date), Some(if(p.closed) 1 else 0))



  //the string is a model name.
  override def openProofs(userId: String): List[ProofPOJO] =
    sqldb.withSession(implicit session => {
      getProofsForUser(userId).map(_._1).filter(!_.closed)
    })

  private def sqliteBoolToBoolean(x : Int) = if(x == 0) false else if(x == 1) true else throw new Exception()

  //returns id of create object
  override def getProofsForModel(modelId: String): List[ProofPOJO] =
    sqldb.withSession(implicit session => {
      Proofs.filter(_.modelid === modelId).list.map(p => {
//        val stepCount : Int = Tacticonproof.filter(_.proofid === p.proofid.get).list.count
        val stepCount = 0 //@todo after everything else is done implement this.
        val closed : Boolean = sqliteBoolToBoolean(p.closed.getOrElse(0))
        new ProofPOJO(p.proofid.get, p.modelid.get, blankOk(p.name), blankOk(p.description), blankOk(p.date), stepCount, closed)
      })
    })


  //Models
  override def createModel(userId: String, name: String, fileContents: String, date: String,
                           description : Option[String]=None, publink:Option[String]=None,
                           title:Option[String]=None, tactic:Option[String]=None) : Option[String] =
    sqldb.withSession(implicit session => {
      if(Models.filter(_.userid === userId).filter(_.name === name).list.length == 0) {
        val modelId = idgen()

        Models.map(m => (m.modelid.get, m.userid.get, m.name.get, m.filecontents.get, m.date.get, m.description, m.publink, m.title, m.tactic))
          .insert(modelId, userId, name, fileContents, date, description, publink, title, tactic)

        Some(modelId)
      }
      else None
    })

  override def createProofForModel(modelId: String, name: String, description: String, date: String): String =
    sqldb.withSession(implicit session => {
      val proofId = idgen()
      Proofs.map(p => (p.proofid.get, p.modelid.get, p.name.get, p.description.get, p.date.get, p.closed.get))
            .insert(proofId, modelId, name, description, date, 0)
      proofId
    })

  override def getModel(modelId: String): ModelPOJO =
    sqldb.withSession(implicit session => {
      val models =
        Models.filter(_.modelid === modelId)
            .list
            .map(m => new ModelPOJO(
              m.modelid.get, m.userid.get, blankOk(m.name), blankOk(m.date), m.filecontents.get, blankOk(m.description), blankOk(m.publink), blankOk(m.title), m.tactic
            ))

      if(models.length < 1) throw new Exception("getModel type should be an Option")
      else if(models.length == 1) models.head
      else throw new Exception("Primary keys aren't unique in models table.")
    })

  override def getUsername(uid: String): String =
    uid

  private def optToString[T](o : Option[T]) = o match {
    case Some(x) => Some(x.toString())
    case None => None
  }

  override def getConfiguration(configName: String): ConfigurationPOJO =
    sqldb.withSession(implicit session => {
      val kvp = Config.filter(_.configname === configName)
        .filter(_.key.isDefined)
        .list
        .map(conf => (conf.key.get, blankOk(conf.value)))
        .toMap

      new ConfigurationPOJO(configName, kvp)
    })

  /**
    * Initializes a new database.
    */
  override def cleanup(): Unit = ???

  /** Deletes an execution from the database */
  override def deleteExecution(executionId: String): Unit = ???

  /** Creates a new execution and returns the new ID in tacticExecutions */
  override def createExecution(proofId: String): String =
    sqldb.withSession(implicit session => {
      val executionId = idgen()
      Tacticexecutions.map(te => (te.executionid.get, te.proofid.get))
        .insert(executionId, proofId)
      executionId
    })

  /** Deletes a provable and all associated sequents / formulas */
  override def deleteProvable(provableId: String): Unit =  ???

  /**
    * Adds an execution step to an existing execution
    * @note Implementations should enforce additional invarants -- never insert when branches or alt orderings overlap.
    */
  override def addExecutionStep(step: ExecutionStepPOJO): String = {
    val (branchOrder: Int, branchLabel) = (step.branchOrder, step.branchLabel) match {
      case (None, None) => (null, null)
      case (Some(order), None) => (order, null)
      case (None, Some(label)) => (null, label)
      case (Some(order), Some(label)) =>
        throw new Exception("execution steps cannot have both a branchOrder and a branchLabel")
    }
    sqldb.withSession(implicit session => {
      val executionStepId = idgen()
      val status = ExecutionStepStatus.toString(step.status)
      // @TODO See if Nathan confirms that the db schema has the wrong type
      val hack = 0
      Executionsteps.map({case step => (step.stepid.get, step.executionid.get, step.previousstep.get, step.parentstep.get,
        step.branchorder.get, step.branchlabel.get, step.alternativeorder.get, step.status.get, step.executableid.get,
        step.inputprovableid.get, step.resultprovableid.get, step.userexecuted.get)})
      .insert((executionStepId, step.executionId, step.previousStep, step.parentStep, branchOrder, branchLabel,
        step.alternativeOrder, status, step.executableId, step.inputProvableId, step.resultProvableId,
        step.userExecuted.toString))
      executionStepId
    })
  }

  /** Adds a Bellerophon expression as an executable and returns the new executableId */
  override def addBelleExpr(expr: BelleExpr, params: List[ParameterPOJO]): String =
    sqldb.withSession(implicit session => {
      // @TODO Figure out whether to generate ID's here or pass them in through the params
      val executableId = idgen()
      Executables.map({case exe => (exe.executableid.get, exe.scalatacticid, exe.belleexpr)})
      .insert((executableId, None, Some(expr.toString)))
      val paramTable = Executableparameter.map({case param => (param.parameterid.get, param.executableid.get, param.idx.get,
        param.valuetype.get, param.value.get)})
      for (i <- params.indices) {
        val paramId = idgen()
        paramTable.insert((paramId, executableId, i, params(i).valueType.toString, params(i).value))
      }
      executableId
    })

  /** @TODO what if we want to extract a proof witness from a deserialized provable? Doesn't this put the
    * DB into the prover core in a way?*/
  /** Stores a Provable in the database and returns its ID */
  override def serializeProvable(p: Provable): String = {
    val provableId = idgen()
    val sequentId = idgen()
    val ante = p.conclusion.ante
    val succ = p.conclusion.succ
    sqldb.withSession(implicit session => {
      Provables.map({case provable => (provable.provableid.get, provable.conclusionid.get)})
      .insert((provableId, sequentId))
      Sequents.map({case sequent => (sequent.sequentid.get, sequent.provableid.get)})
      .insert((sequentId, provableId))
      val formulas = Sequentformulas.map({case fml => (fml.sequentformulaid.get, fml.sequentid.get,
        fml.isante.get, fml.idx.get, fml.formula.get)})
      for(i <- ante.indices) {
        formulas.insert((idgen(), sequentId, true.toString, i, ante(i).toString))
      }
      for(i <- succ.indices) {
        formulas.insert((idgen(), sequentId, false.toString, i, succ(i).toString))
      }
      provableId
    })}

  /** Returns the executable with ID executableId */
  override def getExecutable(executableId: String): ExecutablePOJO =
    sqldb.withSession(implicit session => {
      val executables =
        Executables.filter(_.executableid === executableId)
          .list
          .map(exe => new ExecutablePOJO(exe.executableid.get, exe.scalatacticid, exe.belleexpr))
      if(executables.length < 1) throw new Exception("getExecutable type should be an Option")
      else if(executables.length == 1) executables.head
      else throw new Exception("Primary keys aren't unique in executables table.")
    })

  /** Use escape hatch in prover core to create a new Provable */
  override def loadProvable(provableId: String): Sequent = ???

  override def getExecutionSteps(executionID: String): List[ExecutionStepPOJO] = {
    sqldb.withSession(implicit session => {
      val steps =
      Executionsteps.filter(_.executionid === executionID)
      .list
      .map(step => new ExecutionStepPOJO(step.stepid.get, step.executionid.get, step.previousstep.get, step.parentstep.get,
        step.branchorder, step.branchlabel, step.alternativeorder.get, ExecutionStepStatus.fromString(step.status.get),
        step.executableid.get, step.inputprovableid.get, step.resultprovableid.get, step.userexecuted.get.toBoolean))
    if(steps.length < 1) throw new Exception("No steps found for execution " + executionID)
    else steps
  })}

  /** Adds a new scala tactic and returns the resulting id */
  /*@TODO Understand whether to use the ID passed in or generate our own*/
  override def addScalaTactic(scalaTactic: ScalaTacticPOJO): String = {
    val scalaTacticId = idgen()
    sqldb.withSession(implicit session => {
      Scalatactics.map({case tactic => (tactic.scalatacticid.get, tactic.location.get)})
      .insert((scalaTacticId, scalaTactic.location))
      scalaTacticId
    })
  }

  /** @TODO Clarify spec for this function. Questions:
    * Top-level rules only?
    * Branches?
    * Alternatives?
    * Does order matter?
    * What's in each string? */
  override def getProofSteps(proofId: String): List[String] = ???

  /** Adds a built-in tactic application using a set of parameters */
  override def addAppliedScalaTactic(scalaTacticId: String, params: List[ParameterPOJO]): String = {
    val executableId = idgen()
    sqldb.withSession(implicit session => {
      Executables.map({case exe => (exe.executableid.get, exe.scalatacticid, exe.belleexpr)})
        .insert((executableId, Some(scalaTacticId), None))
      val paramTable = Executableparameter.map({case param => (param.parameterid.get, param.executableid.get, param.idx.get,
        param.valuetype.get, param.value.get)})
      for (i <- params.indices) {
        val paramId = idgen()
        paramTable.insert((paramId, executableId, i, params(i).valueType.toString, params(i).value))
      }
      executableId})
  }

  /** Updates an executable step's status. @note should not be transitive */
  override def updateExecutionStatus(executionStepId: String, status: ExecutionStepStatus): Unit = {
    val newStatus = ExecutionStepStatus.toString(status)
    sqldb.withSession(implicit session => {
      Executionsteps.filter(_.stepid === executionStepId).map(_.status).update(Some(newStatus))
    })
  }

  private def sortFormulas(fromAnte: Boolean, formulas: List[SequentFormulaPOJO]): List[Formula] = {
    import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
    val relevant = formulas.filter({case formula => fromAnte == formula.isAnte})
    val sorted = relevant.sortWith({case (f1, f2) => f1.index > f2.index})
    sorted.map({case formula => formula.formulaStr.asFormula})
  }

  /** Gets the conclusion of a provable */
  override def getConclusion(provableId: String): Sequent = {
    sqldb.withSession(implicit session => {
      val sequents =
        Sequents.filter(_.provableid === provableId)
        .list
        .map({case sequent => sequent.sequentid.get})
      if (sequents.length != 1)
        throw new Exception ("provable should have exactly 1 sequent in getConclusion, has " + sequents.length)
      val sequent = sequents.head
      val formulas =
        Sequentformulas.filter(_.sequentid === sequent)
          .list
          .map(formula => new SequentFormulaPOJO(formula.sequentformulaid.get, formula.sequentid.get,
            formula.isante.get.toBoolean, formula.idx.get, formula.formula.get))
      val ante = sortFormulas(fromAnte=true, formulas).toIndexedSeq
      val succ = sortFormulas(fromAnte=false, formulas).toIndexedSeq
      Sequent(null, ante, succ)
    })
  }
}
