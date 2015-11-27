/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.hydra

import java.io.FileOutputStream
import java.nio.channels.Channels
import java.sql.SQLException

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.core.{SuccPos, Formula, Provable, Sequent}
import edu.cmu.cs.ls.keymaerax.hydra.ExecutionStepStatus.ExecutionStepStatus
import edu.cmu.cs.ls.keymaerax.tactics.PosInExpr

import scala.collection.immutable.Nil

//import Tables.TacticonproofRow
import edu.cmu.cs.ls.keymaerax.api.KeYmaeraInterface
import scala.slick.jdbc.StaticQuery.interpolation
import scala.slick.driver.SQLiteDriver.simple._
import scala.slick.lifted.{ProvenShape, ForeignKeyQuery}
import edu.cmu.cs.ls.keymaerax.api.KeYmaeraInterface.PositionTacticAutomation

/**
 * Created by nfulton on 4/10/15.
 */
object SQLite {

  import Tables._

  val ProdDB: SQLiteDB = new SQLiteDB(DBAbstractionObj.dblocation)
  val TestDB: SQLiteDB = new SQLiteDB(DBAbstractionObj.testLocation)

  class SQLiteDB(dblocation: String) extends DBAbstraction {

    val sqldb = Database.forURL("jdbc:sqlite:" + dblocation, driver = "org.sqlite.JDBC")
    private var currentSession:Session = null
    private var nUpdates = 0
    private var nInserts = 0
    private var nSelects = 0

    implicit def session:Session = {
      if (currentSession == null || currentSession.conn.isClosed) {
        currentSession = sqldb.createSession()
        /* Enable write-ahead logging for SQLite - significantly improves write performance */
        sqlu"PRAGMA journal_mode = WAL".execute(currentSession)
        /* @TODO Setting synchronous = OFF ruins fault-tolerance, but right now I'm not sure how else to get the
        * throughput we need. Look for a better way. */
        sqlu"PRAGMA synchronous = OFF".execute(currentSession)
        sqlu"VACUUM".execute(currentSession)
      }
      currentSession
    }

    private def ensureExists(location: String): Unit = {
      if (!new java.io.File(location).exists()) {
        cleanup(location)
      }
    }
    ensureExists(DBAbstractionObj.dblocation)
    ensureExists(DBAbstractionObj.testLocation)

    //@TODO
    // Configuration
    override def getAllConfigurations: Set[ConfigurationPOJO] =
      session.withTransaction({
        nSelects = nSelects + 1
        Config.list.filter(_.configname.isDefined).map(_.configname.get).map(getConfiguration(_)).toSet
      })

    override def createConfiguration(configName: String): Boolean =
      session.withTransaction({
        //This is unnecessary?
        true
      })

    private def blankOk(x: Option[String]): String = x match {
      case Some(y) => y
      case None => ""
    }

    override def getModelList(userId: String): List[ModelPOJO] = {
      session.withTransaction({
        nSelects = nSelects + 1
        Models.filter(_.userid === userId).list.map(element => new ModelPOJO(element.modelid.get, element.userid.get, element.name.get,
          blankOk(element.date), blankOk(element.filecontents),
          blankOk(element.description), blankOk(element.publink), blankOk(element.title), element.tactic))
      })
    }

    override def createUser(username: String, password: String): Unit = {
      session.withTransaction({
        Users.map(u => (u.email.get, u.password.get))
          .insert((username, password))
        nInserts = nInserts + 1
      })}

    private def idgen(): String = java.util.UUID.randomUUID().toString()

    /**
      * Poorly names -- either update the config, or else insert an existing key.
      * But in Mongo it was just update, because of the nested documents thing.
      * @param config
      */
    override def updateConfiguration(config: ConfigurationPOJO): Unit =
      session.withTransaction({
        config.config.map(kvp => {
          val key = kvp._1
          val value = kvp._2
          nSelects = nSelects + 1
          val configExists = Config.filter(c => c.configname === config.name && c.key === key).list.length != 0

          if (configExists) {
            val q = for {l <- Config if (l.configname === config.name && l.key === key)} yield l.value
            q.update(Some(value))
            nUpdates = nUpdates + 1
          }
          else {
            Config.map(c => (c.configname.get, c.key.get, c.value.get))
              .insert((config.name, key, value))
            nInserts = nInserts + 1
          }
        })
      })

    //Proofs and Proof Nodes
    override def getProofInfo(proofId: Int): ProofPOJO =
      session.withTransaction({
        val stepCount = getProofSteps(proofId).size
        nSelects = nSelects + 1
        val list = Proofs.filter(_.proofid === proofId)
          .list
          .map(p => new ProofPOJO(p.proofid.get, p.modelid.get, blankOk(p.name), blankOk(p.description),
            blankOk(p.date), stepCount, p.closed.getOrElse(0) == 1))
        if (list.length > 1) throw new Exception()
        else if (list.length == 0) throw new Exception()
        else list.head
      })

    // Users
    override def userExists(username: String): Boolean =
      session.withTransaction({
        nSelects = nSelects + 1
        Users.filter(_.email === username).list.length != 0
      })


    override def getProofsForUser(userId: String): List[(ProofPOJO, String)] =
      session.withTransaction({
        val models = getModelList(userId)

        models.map(model => {
          val modelName = model.name
          val proofs = getProofsForModel(model.modelId)
          proofs.map((_, modelName))
        }).flatten
      })

    override def checkPassword(username: String, password: String): Boolean =
      session.withTransaction({
        nSelects = nSelects + 1
        Users.filter(_.email === username).filter(_.password === password).list.length != 0
      })

    override def updateProofInfo(proof: ProofPOJO): Unit =
      session.withTransaction({
        nSelects = nSelects + 1
        Proofs.filter(_.proofid === proof.proofId).update(proofPojoToRow(proof))
        nUpdates = nUpdates + 1
      })

    override def updateProofName(proofId: Int, newName: String): Unit = {
      session.withTransaction({
        nSelects = nSelects + 1
        Proofs.filter(_.proofid === proofId).map(_.name).update(Some(newName))
        nUpdates = nUpdates + 1
      })
    }

    //@todo actually these sorts of methods are rather dangerous because any schema change could mess this up.
    private def proofPojoToRow(p: ProofPOJO): ProofsRow = new ProofsRow(Some(p.proofId), Some(p.modelId), Some(p.name), Some(p.description), Some(p.date), Some(if (p.closed) 1 else 0))


    //the string is a model name.
    override def openProofs(userId: String): List[ProofPOJO] =
      session.withTransaction({
        nSelects = nSelects + 1
        getProofsForUser(userId).map(_._1).filter(!_.closed)
      })

    private def sqliteBoolToBoolean(x: Int) = if (x == 0) false else if (x == 1) true else throw new Exception()

    //returns id of create object
    override def getProofsForModel(modelId: Int): List[ProofPOJO] =
      session.withTransaction({
        nSelects = nSelects + 1
        Proofs.filter(_.modelid === modelId).list.map(p => {
          //        val stepCount : Int = Tacticonproof.filter(_.proofid === p.proofid.get).list.count
          val stepCount = 0 //@todo after everything else is done implement this.
          val closed: Boolean = sqliteBoolToBoolean(p.closed.getOrElse(0))
          new ProofPOJO(p.proofid.get, p.modelid.get, blankOk(p.name), blankOk(p.description), blankOk(p.date), stepCount, closed)
        })
      })


    //Models
    override def createModel(userId: String, name: String, fileContents: String, date: String,
                             description: Option[String] = None, publink: Option[String] = None,
                             title: Option[String] = None, tactic: Option[String] = None): Option[Int] =
      session.withTransaction({
        nSelects = nSelects + 1
        if (Models.filter(_.userid === userId).filter(_.name === name).list.length == 0) {
          nInserts = nInserts + 1
          Some(Models.map(m => (m.userid.get, m.name.get, m.filecontents.get, m.date.get, m.description, m.publink, m.title, m.tactic))
            .insert(userId, name, fileContents, date, description, publink, title, tactic))
        }
        else None
      })

    override def createProofForModel(modelId: Int, name: String, description: String, date: String): Int =
      session.withTransaction({
        nInserts = nInserts + 1
        Proofs.map(p => ( p.modelid.get, p.name.get, p.description.get, p.date.get, p.closed.get))
          .insert(modelId, name, description, date, 0)
      })

    override def getModel(modelId: Int): ModelPOJO =
      session.withTransaction({
        nSelects = nSelects + 1
        val models =
          Models.filter(_.modelid === modelId)
            .list
            .map(m => new ModelPOJO(
              m.modelid.get, m.userid.get, blankOk(m.name), blankOk(m.date), m.filecontents.get, blankOk(m.description), blankOk(m.publink), blankOk(m.title), m.tactic
            ))

        if (models.length < 1) throw new Exception("getModel type should be an Option")
        else if (models.length == 1) models.head
        else throw new Exception("Primary keys aren't unique in models table.")
      })

    override def getUsername(uid: String): String =
      uid

    private def optToString[T](o: Option[T]) = o match {
      case Some(x) => Some(x.toString())
      case None => None
    }

    override def getConfiguration(configName: String): ConfigurationPOJO =
      session.withTransaction({
        nSelects = nSelects + 1
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
    override def cleanup (): Unit = { cleanup(DBAbstractionObj.dblocation)}
    def cleanup(which: String): Unit = {
      val dbFile = this.getClass.getResourceAsStream("/keymaerax.sqlite")
      val target = new java.io.File(which)
      val targetStream = new FileOutputStream(target)
      targetStream.getChannel.transferFrom(Channels.newChannel(dbFile), 0, Long.MaxValue)
      targetStream.close()
      dbFile.close()
    }

    /** Deletes an execution from the database */
    override def deleteExecution(executionId: Int): Unit = ???

    /** Creates a new execution and returns the new ID in tacticExecutions */
    override def createExecution(proofId: Int): Int =
      session.withTransaction({
        val executionId =
          Tacticexecutions.map(te => te.proofid.get)
            .insert(proofId)
        nInserts = nInserts + 1
        executionId
      })

    /** Deletes a provable and all associated sequents / formulas */
    override def deleteProvable(provableId: Int): Unit = ???

    /**
      * Adds an execution step to an existing execution
      * @note Implementations should enforce additional invarants -- never insert when branches or alt orderings overlap.
      */
    override def addExecutionStep(step: ExecutionStepPOJO): Int = {
      val (branchOrder: Int, branchLabel) = (step.branchOrder, step.branchLabel) match {
        case (None, None) => (null, null)
        case (Some(order), None) => (order, null)
        case (None, Some(label)) => (null, label)
        case (Some(order), Some(label)) =>
          throw new Exception("execution steps cannot have both a branchOrder and a branchLabel")
      }
      session.withTransaction({
        val status = ExecutionStepStatus.toString(step.status)
        val steps =
          Executionsteps.map({case step => (step.executionid.get, step.previousstep.get, step.parentstep.get,
            step.branchorder.get, step.branchlabel.get, step.alternativeorder.get, step.status.get, step.executableid.get,
            step.inputprovableid.get, step.resultprovableid.get, step.userexecuted.get)
          })
        val stepId = steps
            .insert((step.executionId, step.previousStep, step.parentStep, branchOrder, branchLabel,
              step.alternativeOrder, status, step.executableId, step.inputProvableId, step.resultProvableId,
              step.userExecuted.toString))
        nInserts = nInserts + 1
        stepId
      })
    }

    /** Adds a Bellerophon expression as an executable and returns the new executableId */
    override def addBelleExpr(expr: BelleExpr, params: List[ParameterPOJO]): Int =
      session.withTransaction({
        // @TODO Figure out whether to generate ID's here or pass them in through the params
        val executableId =
        Executables.map({ case exe => (exe.scalatacticid, exe.belleexpr) })
          .insert((None, Some(expr.toString)))
        nInserts = nInserts + 1
        val paramTable = Executableparameter.map({ case param => (param.executableid.get, param.idx.get,
          param.valuetype.get, param.value.get)
        })
        for (i <- params.indices) {
          nInserts = nInserts + 1
          paramTable.insert((executableId, i, params(i).valueType.toString, params(i).value))
        }
        executableId
      })

    /* I originally suspected that the writes alone were slowing us down, but if you enable deduplicateSequents you
     * will see this is not the case. This flag enables a query before every provable creation that checks whether the
     * sequent is already present. This significantly reduces writes to the sequent table, but the select queries end
     * up taking the same length of time and the "is this sequent present" computation takes much much longer
     * than all the queries using the naive algorithm below.
     * Due to the slowness I'm leaving the flag disabled, but leaving the code around since it may be of interest while
     * doing optimizations. */
    private val deduplicateSequents = false
    private var searchTime: Long = 0
    private var processTime: Long = 0
    private def findSequentId(s: Sequent): Option[Int] = {
      if (deduplicateSequents) {
        nSelects = nSelects + 1
        val t1 = System.nanoTime()
        val lst = Sequentformulas.list
        val t2 = System.nanoTime()
        searchTime = searchTime + t2 - t1
        val fmls = lst.filter(row =>
          (row.isante.get.toBoolean && s.ante.exists(p => row.formula.get == p.toString))
         || (!row.isante.get.toBoolean && s.succ.exists(p => row.formula.get == p.toString)))
        val fmlss = fmls.sortWith((row1, row2) => row1.sequentid.get.compare(row2.sequentid.get) > 0).groupBy(row => row.sequentid)
        val ante = s.ante.zipWithIndex
        val succ = s.succ.zipWithIndex
        val which = fmlss.find({case ((_: Option[Int], rows)) =>
          val anteFound =
            ante.forall({case (fml:Formula, int:Int) => rows.exists(row =>
              row.idx.get == int && row.isante.get.toBoolean && row.formula.get == fml.toString)})
          val succFound =
            succ.forall({case (fml:Formula, int:Int) => rows.exists(row =>
              row.idx.get == int && !row.isante.get.toBoolean && row.formula.get == fml.toString)})
          anteFound && succFound})
        val t3 = System.nanoTime()
        processTime = processTime + t3 - t2
        which match {
          case None => None
          case Some((_, Nil)) => None
          case Some((_, (x :: _))) => Some(x.sequentid.get)
        }
      }
      else None
    }

    /** @TODO what if we want to extract a proof witness from a deserialized provable? Doesn't this put the
      *       DB into the prover core in a way? */
    /** Stores a Provable in the database and returns its ID */
    override def serializeProvable(p: Provable): Int = {
      val provableId = idgen()
      val ante = p.conclusion.ante
      val succ = p.conclusion.succ
      session.withTransaction({
        findSequentId(p.conclusion) match {
          case None =>
            val provableId =
              Provables.map({ case provable => () })
                .insert()
            val sequentId =
              Sequents.map({ case sequent => (sequent.provableid.get) })
                .insert(provableId)
            Provables.filter(_.provableid === provableId).map(provable => (provable.conclusionid.get))
            .update(sequentId)
            nInserts = nInserts + 2
            nUpdates = nUpdates + 1
            val formulas = Sequentformulas.map({ case fml => (fml.sequentid.get,
              fml.isante.get, fml.idx.get, fml.formula.get)
            })
            for (i <- ante.indices) {
              nInserts = nInserts + 1
              formulas.insert((sequentId, true.toString, i, ante(i).toString))
            }
            for (i <- succ.indices) {
              nInserts = nInserts + 1
              formulas.insert((sequentId, false.toString, i, succ(i).toString))
            }
            provableId
          case Some(sequentId) =>
            nInserts = nInserts + 1
            Provables.map({ case provable => provable.conclusionid.get })
              .insert(sequentId)
        }
      })
    }

    /** Returns the executable with ID executableId */
    override def getExecutable(executableId: Int): ExecutablePOJO =
      session.withTransaction({
        nSelects = nSelects + 1
        val executables =
          Executables.filter(_.executableid === executableId)
            .list
            .map(exe => new ExecutablePOJO(exe.executableid.get, exe.scalatacticid, exe.belleexpr))
        if (executables.length < 1) throw new Exception("getExecutable type should be an Option")
        else if (executables.length == 1) executables.head
        else throw new Exception("Primary keys aren't unique in executables table.")
      })

    /** Use escape hatch in prover core to create a new Provable */
    override def loadProvable(provableId: Int): Sequent = ???

    override def getExecutionSteps(executionID: Int): List[ExecutionStepPOJO] = {
      session.withTransaction({
        nSelects = nSelects + 1
        val steps =
          Executionsteps.filter(_.executionid === executionID)
            .list
            .map(step => new ExecutionStepPOJO(step.stepid.get, step.executionid.get, step.previousstep.get, step.parentstep.get,
              step.branchorder, step.branchlabel, step.alternativeorder.get, ExecutionStepStatus.fromString(step.status.get),
              step.executableid.get, step.inputprovableid.get, step.resultprovableid.get, step.userexecuted.get.toBoolean))
        if (steps.length < 1) throw new Exception("No steps found for execution " + executionID)
        else steps
      })
    }

    /** Adds a new scala tactic and returns the resulting id */
    /*@TODO Understand whether to use the ID passed in or generate our own*/
    override def addScalaTactic(scalaTactic: ScalaTacticPOJO): Int = {
      session.withTransaction({
        Scalatactics.map({ case tactic => tactic.location.get })
          .insert(scalaTactic.location)
      })
    }

    /** @TODO Clarify spec for this function. Questions:
      *       Top-level rules only?
      *       Branches?
      *       Alternatives?
      *       Does order matter?
      *       What's in each string? */
    override def getProofSteps(proofId: Int): List[String] = ???

    /** Adds a built-in tactic application using a set of parameters */
    override def addAppliedScalaTactic(scalaTacticId: Int, params: List[ParameterPOJO]): Int = {
      session.withTransaction({
        val executableId =
          Executables.map({ case exe => ( exe.scalatacticid, exe.belleexpr) })
            .insert(Some(scalaTacticId), None)
        val paramTable = Executableparameter.map({ case param => (param.executableid.get, param.idx.get,
          param.valuetype.get, param.value.get)
        })
        for (i <- params.indices) {
          paramTable.insert((executableId, i, params(i).valueType.toString, params(i).value))
        }
        executableId
      })
    }

    /** Updates an executable step's status. @note should not be transitive */
    override def updateExecutionStatus(executionStepId: Int, status: ExecutionStepStatus): Unit = {
      val newStatus = ExecutionStepStatus.toString(status)
      session.withTransaction({
        nSelects = nSelects + 1
        nUpdates = nUpdates + 1
        Executionsteps.filter(_.stepid === executionStepId).map(_.status).update(Some(newStatus))
      })
    }

    private def sortFormulas(fromAnte: Boolean, formulas: List[SequentFormulaPOJO]): List[Formula] = {
      import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
      val relevant = formulas.filter({ case formula => fromAnte == formula.isAnte })
      val sorted = relevant.sortWith({ case (f1, f2) => f1.index > f2.index })
      sorted.map({ case formula => formula.formulaStr.asFormula })
    }

    /** Gets the conclusion of a provable */
    override def getConclusion(provableId: Int): Sequent = {
      session.withTransaction({
        nSelects = nSelects + 1
        val sequents =
          Sequents.filter(_.provableid === provableId)
            .list
            .map({ case sequent => sequent.sequentid.get })
        if (sequents.length != 1)
          throw new Exception("provable should have exactly 1 sequent in getConclusion, has " + sequents.length)
        val sequent = sequents.head
        val formulas =
          Sequentformulas.filter(_.sequentid === sequent)
            .list
            .map(formula => new SequentFormulaPOJO(formula.sequentformulaid.get, formula.sequentid.get,
              formula.isante.get.toBoolean, formula.idx.get, formula.formula.get))
        val ante = sortFormulas(fromAnte = true, formulas).toIndexedSeq
        val succ = sortFormulas(fromAnte = false, formulas).toIndexedSeq
        Sequent(null, ante, succ)
      })
    }

    def printStats = {
      println("Updates: " + nUpdates + " Inserts: " + nInserts + " Selects: " + nSelects)
      println("Searching time: " + (searchTime / 1000000000.0) + " Processing Time: " + (processTime / 1000000000.0))
    }
  }
}