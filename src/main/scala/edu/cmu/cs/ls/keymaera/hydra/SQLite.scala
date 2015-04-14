package edu.cmu.cs.ls.keymaera.hydra

import java.sql.SQLException

import Tables.TacticonproofRow
import edu.cmu.cs.ls.keymaera.api.KeYmaeraInterface

import scala.slick.driver.SQLiteDriver.simple._
import scala.slick.lifted.{ProvenShape, ForeignKeyQuery}
import edu.cmu.cs.ls.keymaera.api.KeYmaeraInterface.PositionTacticAutomation

/**
 * Created by nfulton on 4/10/15.
 */
object SQLite extends DBAbstraction {

  import Tables._

  val dblocation = System.getProperty("user.home") + "/keymaerax.sqlite3"

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

  /**
   * Initializes a new database.
   */

  override def cleanup(): Unit = {
    sqldb.withSession(implicit session => {
      try {
        ddl.drop
      } catch {
        case e : SQLException => println("Ignoring an exception when dropping DB")//Tables did not exist -- that's find, we create it below anyways. @todo but we are assuming all or no ables exist.
      };
      ddl.create
      this.initializeForDemo()
    })
  }



  private def blankOk(x : Option[String]):String = x match {
    case Some(y) => y
    case None    => ""
  }

  override def getModelList(userId: String): List[ModelPOJO] = {
    sqldb.withSession(implicit session => {
      Models.list.map(element => new ModelPOJO(element.modelid.get, element.userid.get, element.name.get,
        blankOk(element.date), blankOk(element.filecontents),
        blankOk(element.description), blankOk(element.publink), blankOk(element.title)))
    })
  }


  override def getDispatchedTermOrTactic(tId: String): Option[AbstractDispatchedPOJO] =
    sqldb.withSession(implicit session => {
      getDispatchedTactics(tId) match {
        case Some(x) => Some(x)
        case None => getDispatchedCLTerm(tId)
      }
    })

  override def getTactic(id: String): Option[TacticPOJO] =
    sqldb.withSession(implicit session => {
      val matches =
        Tactics.filter(_.tacticid === id)
               .list
               .map(t => new TacticPOJO(t.tacticid.get, t.name.get, t.clazz.get, TacticKind.withName(blankOk(t.kind))))

      if(matches.length > 1) throw new Exception()
      else if(matches.length == 1) Some(matches.head)
      else None
    })


  override def createDispatchedCLTerm(taskId: String, nodeId: Option[String], clTerm: String): String =
    sqldb.withSession(implicit session => {
      val cltermId = idgen()
      Clterms.map(t => (t.termid.get, t.proofid.get, t.nodeid, t.clterm.get))
             .insert(cltermId, taskId, nodeId, clTerm);
      cltermId
    })

  override def updateProofOnTacticCompletion(proofId: String, tId: String): Unit =
    sqldb.withSession(implicit session => {
      val openGoals = KeYmaeraInterface.getOpenGoalCount(proofId)

      val newIdx : Int =
        if (Completedtasks.filter(_.proofid === proofId).filter(_.termid === tId).list.nonEmpty)
          Completedtasks.filter(_.proofid === proofId).filter(_.termid === tId).list.map(_.idx).max + 1
        else 0

      val dispatchedTactic = getDispatchedTermOrTactic(tId)

      dispatchedTactic match {
          //Update the running and completed task lists.
        case Some(x: DispatchedTacticPOJO) => {
          Completedtasks.map(t => (t.stepid, t.proofid.get, t.idx, t.termid, t.prooftacticid.get))
                        .insert(idgen(), proofId, newIdx, None, tId)
          val q = for{l <- Tacticonproof if(l.prooftacticid === tId)} yield l.status
          q.update(Some(DispatchedTacticStatus.Finished.toString))
        }
        case Some(x : DispatchedCLTermPOJO) => {

          Completedtasks.map(t => (t.stepid, t.proofid.get, t.idx, t.termid.get, t.prooftacticid))
            .insert(idgen(), proofId, newIdx, tId, None)
          val q = for{l <- Clterms if(l.termid === tId)} yield l.status
          q.update(Some(DispatchedTacticStatus.Finished.toString))
        }
      }

      //Update the proof statis the proof is complete.
      if(openGoals == 0) {
        val q = for{l <- Proofs if(l.proofid === proofId)} yield l.closed
        q.update(Some(1))
      }
    })

  override def updateDispatchedTactics(tactic: DispatchedTacticPOJO): Unit =
    sqldb.withSession(implicit session => {
      //Create a new row.
      val newRow : TacticonproofRow = TacticonproofRow(Some(tactic.id), Some(tactic.proofId), Some(tactic.tacticsId), tactic.nodeId, tactic.formulaId, optToString(tactic.auto), Some(tactic.status.toString))
      //Commit the new row.
      Tacticonproof.filter(_.prooftacticid === tactic.id).update(newRow)
    })

  override def createUser(username: String, password: String): Unit =
    sqldb.withSession(implicit session => {
      Users.map(u => (u.userid.get, u.email.get, u.password.get))
        .insert((idgen, username, password))
    })


  private def idgen() = java.util.UUID.randomUUID().toString()


  override def updateDispatchedCLTerm(termToUpdate: DispatchedCLTermPOJO): Unit =
    sqldb.withSession(implicit session => {
      Clterms.filter(_.termid === termToUpdate.id).update(termPojoToRow(termToUpdate))
    })

  private def termPojoToRow(t : DispatchedCLTermPOJO) : CltermsRow =
    new CltermsRow(Some(t.id), Some(t.clTerm), Some(t.proofId), t.nodeId, optToString(t.status))

  // Tactics
  override def createTactic(name: String, clazz: String, kind: TacticKind.Value): String =
    sqldb.withSession(implicit session => {
      val id = idgen()
      Tactics.map(t => (t.tacticid.get, t.name.get, t.clazz.get, t.kind.get))
             .insert(id, name, clazz, kind.toString());
      id
    })


  override def updateProofOnCLTermCompletion(proofId: String, termId: String): Unit =
    updateProofOnTacticCompletion(proofId, termId) //@TODO check this.

  override def getTacticByName(name: String): Option[TacticPOJO] =
    sqldb.withSession(implicit session => {
      Tactics.filter(_.name === name).firstOption match {
        case Some(x) => getTactic(x.tacticid.get)
        case None => None
      }
    })


  override def updateConfiguration(config: ConfigurationPOJO): Unit =
    sqldb.withSession(implicit session => {
      //Wow that's a pain.
      config.config.map(kvp => {
        val key = kvp._1
        val value = kvp._2
        val q = for {l <- Config if(l.configname === config.name && l.key === key)} yield l.value
        q.update(Some(value))
      })
    })


  //Proofs and Proof Nodes
  override def getProofInfo(proofId: String): ProofPOJO =
    sqldb.withSession(implicit session => {
      val stepCount = 0 //@todo when everything else is done, do this.
      val list = Proofs.filter(_.proofid === proofId)
            .list
            .map(p => new ProofPOJO(p.proofid.get, p.modelid.get, blankOk(p.name), blankOk(p.description),
                                    blankOk(p.date), stepCount, p.closed.getOrElse(0) == 0))
      if(list.length > 1) throw new Exception()
      else if(list.length == 0) throw new Exception()
      else list.head
    })

  override def getProofSteps(proofId: String): List[String] =
    sqldb.withSession(implicit session => {
      Completedtasks.filter(_.proofid === proofId).sortBy(_.idx).list.map(_.stepid)
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
  override def createModel(userId: String, name: String, fileContents: String, date: String): Boolean =
    sqldb.withSession(implicit session => {
      if(Models.filter(_.userid === userId).filter(_.name === name).list.length == 0) {
        def modelId = idgen()

        Models.map(m => (m.modelid.get, m.userid.get, m.name.get, m.filecontents.get, m.date.get))
          .insert(modelId, userId, name, fileContents, date)
        true
      }
      else false
    })


  override def getDispatchedCLTerm(id: String): Option[DispatchedCLTermPOJO] =
    sqldb.withSession(implicit session => {
      val list = Clterms.filter(_.termid === id)
             .list
             .map(t => new DispatchedCLTermPOJO(t.termid.get, t.proofid.get, t.nodeid, t.clterm.get,
                t.status match {
                  case Some(x) => Some(DispatchedTacticStatus.withName(x))
                  case None => None
                }))

      if(list.length == 0) None
      else if(list.length != 1) throw new Exception()
      else Some(list.head)
    })

  override def createProofForModel(modelId: String, name: String, description: String, date: String): String =
    sqldb.withSession(implicit session => {
      val proofId = idgen()
      Proofs.map(p => (p.proofid.get, p.modelid.get, p.name.get, p.description.get, p.date.get, p.closed.get))
            .insert(proofId, modelId, name, description, date, 0)
      proofId
    })

  override def tacticExists(id: String): Boolean =
    sqldb.withSession(implicit session => {
      Tactics.filter(_.tacticid === id).list.length != 0
    })

  override def getModel(modelId: String): ModelPOJO =
    sqldb.withSession(implicit session => {
      val models =
        Models.filter(_.modelid === modelId)
            .list
            .map(m => new ModelPOJO(
              m.modelid.get, m.userid.get, blankOk(m.name), blankOk(m.date), m.filecontents.get, blankOk(m.description), blankOk(m.publink), blankOk(m.title)
            ))

      if(models.length < 1) throw new Exception("getModel type should be an Option")
      else if(models.length == 1) models.head
      else throw new Exception("Primary keys aren't unique in models table.")
    })

  override def getTactics: List[TacticPOJO] =
    sqldb.withSession(implicit session => {
      Tactics.list.map(t => new TacticPOJO(
        t.tacticid.get, blankOk(t.name), t.clazz.get, TacticKind.withName(t.kind.getOrElse(""))
      ))
    })

  override def getUsername(uid: String): String =
    uid

  private def optToString[T](o : Option[T]) = o match {
    case Some(x) => Some(x.toString())
    case None => None
  }

  override def createDispatchedTactics(taskId:String, nodeId:Option[String], formulaId:Option[String], tacticsId:String,
                              input:Map[Int, String], auto: Option[PositionTacticAutomation.PositionTacticAutomation],
                              status:DispatchedTacticStatus.Value) : String =
    sqldb.withSession(implicit session => {
      val id = idgen()

      //First create the dispatched tactic
      Tacticonproof.map(tp => (tp.prooftacticid.get, tp.proofid.get, tp.nodeid, tp.formulaid, tp.tacticsid.get, tp.auto, tp.status.get))
        .insert((id, taskId, nodeId, formulaId, tacticsId, optToString(auto), status.toString()))

      input.toList.map(element => {
        Prooftacticinput.map(i => (i.prooftacticid.get, i.inputorder.get, i.input.get))
        .insert((id, element._1, element._2))
      })

      id
    })

  override def getDispatchedTactics(tId: String): Option[DispatchedTacticPOJO] =
    sqldb.withSession(implicit session => {
      val result = Tacticonproof.filter(_.prooftacticid === tId)
        .list
        .map(element => {
          //get Inputs.
          val inputs : Map[Int, String] = Prooftacticinput
            .filter(input => input.prooftacticid === element.prooftacticid)
            .list
            .map(element => (element.inputorder.get, blankOk(element.input))).toMap

          val auto = element.auto match {
            case Some(a) => Some(PositionTacticAutomation.withName(a))
            case None => None
          }

          DispatchedTacticPOJO(element.prooftacticid.get, element.proofid.get, element.nodeid, element.formulaid,
            element.tacticsid.get, inputs, auto,
            DispatchedTacticStatus.fromString(element.status.get))
        })

      if(result.length < 1) None
      else if(result.length == 1) Some(result.head)
      else throw new Exception("Expected primary keys to be unique.")
    })


  override def getConfiguration(configName: String): ConfigurationPOJO =
    sqldb.withSession(implicit session => {
      val kvp = Config.filter(_.configname === configName)
        .filter(_.key.isDefined)
        .list
        .map(conf => (conf.key.get, blankOk(conf.value)))
        .toMap

      new ConfigurationPOJO(configName, kvp)
    })
}

//
//object SQLiteTables {
//  class ConfigTable(tag : Tag) extends Table[(String, String,String,String)](tag, "config") {
//    def configId   = column[String]("configId", O.PrimaryKey, O.NotNull)
//    def configName = column[String]("configName", O.NotNull)
//    def key = column[String]("configName", O.NotNull)
//    def value = column[String]("configName", O.NotNull)
//
//    override def * : ProvenShape[(String, String, String, String)] = (configId, configName, key, value)
//  }
//
////  class Tactics(tag : Tag) extends Table[(String, String, String, String)](tag, "tactics") {
////    def tacticId = column[String]("tacticId", O.PrimaryKey, O.NotNull)
////    def name = column[String]("name", O.NotNull)
////    def clazz = column[String]("clazz", O.NotNull)
////    def kind = column[String]("kind", O.NotNull)
////
////    override def * : ProvenShape[(String,String,String,String)] = (tacticId, name, clazz, kind)
////  }
////
////  class Users(tag : Tag) extends Table[(String, String, String)](tag, "users") {
////    def userId = column[String]("userId", O.PrimaryKey, O.NotNull)
////    def email = column[String]("email", O.NotNull)
////    def password = column[String]("password", O.NotNull)
////    def acceptedTerms = column[String]("acceptedTerms", O.NotNull)
////
////    override def * : ProvenShape[(String,String,String, String)] = (userId, email, password, acceptedTerms)
////  }
////
////  class Models(tag : Tag) extends Table[(String, String, String)](tag, "models") {
////    def modelId = column[String]("modelId", O.PrimaryKey, O.NotNull)
////    def userId = column[String]("userId", O.NotNull)
////    def name = column[String]("name", O.NotNull)
////    def date = column[String]("date")
////    def description = column[String]("description")
////    def fileContents = column[String]("fileContents")
////    def pubLink = column[String]("pubLink")
////    def title = column[String]("title")
////
////    override def * : ProvenShape[(String,String,String,String,String,String,String,String)] = (modelId, userId, name, date, description, fileContents, pubLink, title)
////  }
////
////  class Proofs(tag : Tag) extends Table[(String,String,String,String,String,String,Boolean)](tag, "proofs") {
////    def proofId = column[String]("proofId", O.PrimaryKey, O.NotNull)
////    def modelId = column[String]("modelId", O.NotNull)
////    def name = column[String]("name", O.NotNull)
////    def description = column[String]("description")
////    def date = column[String]("date")
////    def closed = column[Boolean]("closed")
////
////    override def * : ProvenShape[(String,String,String,String,String,Boolean)] = (proofId, modelId, name, description, date, closed)
////  }
//
//  //A built-in tactic run on a proof.
////  class TacticOnProof(tag : Tag) extends Table[(String, String, String, String, String, String)](tag, "tacticOnProof") {
////    def proofTacticId = column[String]("proofTacticId", O.PrimaryKey, O.NotNull)
////    def proofId = column[String]("proofId", O.PrimaryKey, O.NotNull)
////  }
//
//
//}