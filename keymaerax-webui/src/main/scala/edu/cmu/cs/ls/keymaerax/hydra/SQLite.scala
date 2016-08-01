/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.hydra

import java.io.{File, FileOutputStream}
import java.nio.channels.Channels
import java.security.SecureRandom
import java.sql.{Blob, SQLException}
import javax.crypto.SecretKeyFactory
import javax.crypto.spec.PBEKeySpec
import javax.xml.bind.DatatypeConverter

import edu.cmu.cs.ls.keymaerax.bellerophon.{BTacticParser, BelleProvable, SequentialInterpreter, BelleExpr}
import _root_.edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary
import _root_.edu.cmu.cs.ls.keymaerax.core._
import _root_.edu.cmu.cs.ls.keymaerax.hydra.ExecutionStepStatus.ExecutionStepStatus
import edu.cmu.cs.ls.keymaerax.lemma.{LemmaDB, LemmaDBFactory}
import _root_.edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXExtendedLemmaParser, ProofEvidence, KeYmaeraXProblemParser}
import _root_.edu.cmu.cs.ls.keymaerax.tools.ToolEvidence
import edu.cmu.cs.ls.keymaerax.core.{SuccPos, Formula, Provable, Sequent}

import scala.collection.immutable.Nil

//import Tables.TacticonproofRow
import scala.slick.jdbc.StaticQuery.interpolation
import scala.slick.driver.SQLiteDriver.simple._
import scala.slick.lifted.{ProvenShape, ForeignKeyQuery}

/**
 * Created by nfulton on 4/10/15.
 */
object SQLite {

  import Tables._

  val ProdDB: SQLiteDB = new SQLiteDB(DBAbstractionObj.dblocation)
  /** Use this for all unit tests that work with the database, so tests don't infect the production database */
  val TestDB: SQLiteDB = new SQLiteDB(DBAbstractionObj.testLocation)

  /** LemmaDB using SQLite for storage. All provables that truly need to be persistent should be stored here, as this will
    * survive .keymaerax/cache being deleted.
    *
    * Because parsing lemmas is a relatively expensive operation (a page load can request dozens of provables, which
    * can take seconds), parsing operations are cached internally. All accesses to the lemma table must use this class
    * in order for the cache to always be up to date. */
  class SQLiteLemmaDB (db: SQLiteDB) extends LemmaDB {
    override def contains(id: LemmaID): Boolean = get(id) match {
      case Some(x) => true
      case _ => false
    }

    private var cachedLemmas: Map[Int, Lemma] = Map.empty

    override def get(id: LemmaID): Option[Lemma] = {
      get(List(id.toInt)).map(_.head)
    }

    def get(ids: List[Int]): Option[List[Lemma]] = {
      val lemmaOptions =
        ids.map{case id =>
          cachedLemmas.get(id) match {
            case Some(lemma) => Some(lemma)
            case None =>
              db.getLemma(id).map(Lemma.fromString) match {
                case Some(lemma) =>
                  cachedLemmas = cachedLemmas.+((id, lemma))
                  Some(lemma)
                case None => None
              }
          }
        }
      if(lemmaOptions.forall(_.isDefined))
        Some(lemmaOptions.map(_.get))
      else
        None
    }

    private val REDUNDANT_CHECKS = false

    private def saveLemma(lemma:Lemma, id:Int): Unit = {
      if (REDUNDANT_CHECKS) {
        //@see[[edu.cmu.cs.ls.keymaerax.core.Lemma]]
        val parse = KeYmaeraXExtendedLemmaParser(addRequiredEvidence(lemma).toString)
        assert(parse._1 == lemma.name, "reparse of printed lemma's name should be identical to original lemma")
        assert(parse._2 == lemma.fact.conclusion +: lemma.fact.subgoals, s"reparse of printed lemma's fact ${lemma.fact.conclusion +: lemma.fact.subgoals}should be identical to original lemma ${parse._2}")
        assert(parse._3 == lemma.evidence, "reparse of printed lemma's evidence should be identical to original lemma")
      }

      val lemmaToAdd = addRequiredEvidence(lemma)
      val lemmaString = lemmaToAdd.toString

      db.updateLemma(id, lemmaString)
      cachedLemmas = cachedLemmas.+((id, lemmaToAdd))
      val lemmaFromDB = get(id.toString)
      if (lemmaFromDB.isEmpty || lemmaFromDB.get != lemmaToAdd) {
        db.deleteLemma(id)
        cachedLemmas = cachedLemmas.-(id)
        throw new IllegalStateException("Lemma in DB differed from lemma in memory -> deleted")
      }
      // assertion duplicates condition and throw statement
      assert(lemmaFromDB.isDefined && lemmaFromDB.get == lemmaToAdd, "Lemma stored in DB should be identical to lemma in memory " + lemma)
    }

    private def isUniqueLemmaId(id: Int) = db.getLemmas(List(id)).isEmpty

    override def add(lemma: Lemma): LemmaID = {
      val id = this.synchronized {
        // synchronize to make sure concurrent uses use new rows
        lemma.name match {
          case Some(n) =>
            require(isUniqueLemmaId(n.toInt) || lemma == get(n).orNull,
            "Lemma name '" + n + ".alp' must be unique, or file content must be the lemma: \n" + lemma)
            n.toInt
          case None =>  db.createLemma()
        }
      }
      saveLemma(lemma, id)
      id.toString
    }

    override def remove(name: String): Boolean = {
      ???
    }

    override def deleteDatabase(): Unit = {
      db.deleteAllLemmas()
      cachedLemmas = Map.empty
    }
  }


  class SQLiteDB(val dblocation: String) extends DBAbstraction {
    val sqldb = Database.forURL("jdbc:sqlite:" + dblocation, driver = "org.sqlite.JDBC")
    val lemmaDB = new SQLiteLemmaDB(this)
    private var currentSession:Session = null
    /* Statistics on the number of SQL operations performed in this session, useful for profiling. */
    private var nUpdates = 0
    private var nInserts = 0
    private var nSelects = 0

    implicit def session:Session = {
      if (currentSession == null || currentSession.conn.isClosed) {
        currentSession = sqldb.createSession()
        /* Enable write-ahead logging for SQLite - significantly improves write performance */
        sqlu"PRAGMA journal_mode = WAL".execute(currentSession)
        /* Note: Setting synchronous = NORMAL introduces some risk of database corruption during power loss. According
         * to official documentation, that risk is less than the risk of the hard drive failing completely, but we
         * should at least be aware that the risk exists. Initial testing showed this to be about 8 times faster, so
         * it seems worth the risk. */
        sqlu"PRAGMA synchronous = NORMAL".execute(currentSession)
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

    /* withTransaction is not thread-safe if you reuse connections, it will raise an exception saying we're in autocommit
     * mode when we shouldn't be. So only ever call withTransaction inside a synchronized block. */
    def synchronizedTransaction[T](f: => T)(implicit session:Session): T =
      synchronized {
        session.withTransaction(f)
    }

    override def syncDatabase():Unit = {
      sqlu"PRAGMA wal_checkpoint(FULL)".execute(session)
    }

    // Configuration
    override def getAllConfigurations: Set[ConfigurationPOJO] =
      synchronizedTransaction({
        nSelects = nSelects + 1
        Config.list.filter(_.configname.isDefined).map(_.configname.get).map(getConfiguration(_)).toSet
      })

    private def blankOk(x: Option[String]): String = x match {
      case Some(y) => y
      case None => ""
    }

    override def getModelList(userId: String): List[ModelPOJO] = {
      synchronizedTransaction({
        nSelects = nSelects + 1
        Models.filter(_.userid === userId).list.map(element => new ModelPOJO(element._Id.get, element.userid.get, element.name.get,
          blankOk(element.date), blankOk(element.filecontents),
          blankOk(element.description), blankOk(element.publink), blankOk(element.title), element.tactic, getNumProofs(element._Id.get)))
      })
    }

    private def getNumProofs(modelId: Int): Int = {
      Proofs.filter(_.modelid === modelId).length.run
    }

    private def configWithDefault(config: String, subconfig: String, default: Int): Int = {
      try {
        getConfiguration(config).config(subconfig).toInt
      } catch {case (_: NoSuchElementException) =>
        default
      }
    }
    override def createUser(username: String, password: String): Unit = {
      /* Store passwords as a salted hash. Allow configuring number of iterations
       * since we may conceivably want to change it after deployment for performance reasons */
      val iterations = configWithDefault("security", "passwordHashIterations", 10000)
      val saltLength = configWithDefault("security", "passwordSaltLength", 512)
      val (hash, salt) = Password.generateKey(password, iterations, saltLength)
      synchronizedTransaction({
        Users.map(u => (u.email.get, u.hash.get, u.salt.get, u.iterations.get))
          .insert((username, hash, salt, iterations))
        nInserts = nInserts + 1
        copyTutorialModels(username)
      })}

    private def copyTutorialModels(userId: String): Unit = {
      val tutorialModels = Models.filter(_._Id <= 14).list.map(element => new ModelPOJO(element._Id.get, element.userid.get, element.name.get,
        blankOk(element.date), blankOk(element.filecontents),
        blankOk(element.description), blankOk(element.publink), blankOk(element.title), element.tactic, getNumProofs(element._Id.get)))
      tutorialModels.foreach(m => createModel(userId, m.name, m.keyFile, m.date, Some(m.description), Some(m.pubLink), Some(m.title), m.tactic))
    }

    /**
      * Poorly named -- either update the config, or else insert an existing key.
      * But in Mongo it was just update, because of the nested documents thing.
      * @param config
      */
    override def updateConfiguration(config: ConfigurationPOJO): Unit =
      synchronizedTransaction({
        config.config.foreach(kvp => {
          val key = kvp._1
          val value = kvp._2
          nSelects = nSelects + 1
          val configExists = Config.filter(c => c.configname === config.name && c.key === key).list.nonEmpty

          if (configExists) {
            val q = for {l <- Config if l.configname === config.name && l.key === key} yield l.value
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
      synchronizedTransaction({
        val stepCount = describeProofSteps(proofId).size
        nSelects = nSelects + 1
        val list = Proofs.filter(_._Id === proofId)
          .list
          .map(p => new ProofPOJO(p._Id.get, p.modelid.get, blankOk(p.name), blankOk(p.description),
            blankOk(p.date), stepCount, p.closed.getOrElse(0) == 1))
        if (list.length > 1) throw new Exception("Duplicate proof " + proofId)
        else if (list.isEmpty) throw new Exception("Proof not found: " + proofId)
        else list.head
      })

    // Users
    override def userExists(username: String): Boolean =
      synchronizedTransaction({
        nSelects = nSelects + 1
        Users.filter(_.email === username).list.nonEmpty
      })


    override def getProofsForUser(userId: String): List[(ProofPOJO, String)] =
      synchronizedTransaction({
        val models = getModelList(userId)

        models.flatMap(model => {
          val modelName = model.name
          val proofs = getProofsForModel(model.modelId)
          proofs.map((_, modelName))
        })
      })

    override def checkPassword(username: String, password: String): Boolean =
      synchronizedTransaction({
        nSelects = nSelects + 1
        Users.filter(_.email === username).list.exists({case row =>
          val hash = Password.hash(password.toCharArray, row.salt.get.getBytes("UTF-8"), row.iterations.get)
          Password.hashEquals(hash, row.hash.get)
        })
      })

    override def updateProofInfo(proof: ProofPOJO): Unit =
      synchronizedTransaction({
        nSelects = nSelects + 1
        Proofs.filter(_._Id === proof.proofId).update(proofPojoToRow(proof))
        nUpdates = nUpdates + 1
      })

    override def updateProofName(proofId: Int, newName: String): Unit = {
      synchronizedTransaction({
        nSelects = nSelects + 1
        Proofs.filter(_._Id === proofId).map(_.name).update(Some(newName))
        nUpdates = nUpdates + 1
      })
    }

    private def proofPojoToRow(p: ProofPOJO): ProofsRow =
      new ProofsRow(_Id = Some(p.proofId), modelid = Some(p.modelId), name = Some(p.name)
        , description = Some(p.description), date =Some(p.date), closed = Some(if (p.closed) 1 else 0))


    override def openProofs(userId: String): List[ProofPOJO] =
      synchronizedTransaction({
        nSelects = nSelects + 1
        getProofsForUser(userId).map(_._1).filter(!_.closed)
      })

    private def sqliteBoolToBoolean(x: Int) = if (x == 0) false else if (x == 1) true else throw new Exception()

    //returns id of create object
    override def getProofsForModel(modelId: Int): List[ProofPOJO] =
      synchronizedTransaction({
        nSelects = nSelects + 1
        Proofs.filter(_.modelid === modelId).list.map(p => {
          val stepCount = describeProofSteps(p._Id.get).size
          val closed: Boolean = sqliteBoolToBoolean(p.closed.getOrElse(0))
          new ProofPOJO(p._Id.get, p.modelid.get, blankOk(p.name), blankOk(p.description), blankOk(p.date), stepCount, closed)
        })
      })

    def deleteExecution(executionId: Int) = synchronizedTransaction({
      val deletedExecutionSteps = Executionsteps.filter(_.executionid === executionId).delete == 1
      val deletedExecution = Tacticexecutions.filter(_._Id === executionId).delete == 1
      deletedExecutionSteps && deletedExecution
    })

    override def deleteProof(proofId: Int) =
      synchronizedTransaction({
        Tacticexecutions.filter(x => x.proofid === proofId).foreach(f => deleteExecution(f._Id.get))
        Proofs.filter(x => x._Id === proofId).delete == 1
      })

    //Models
    override def createModel(userId: String, name: String, fileContents: String, date: String,
                             description: Option[String] = None, publink: Option[String] = None,
                             title: Option[String] = None, tactic: Option[String] = None): Option[Int] =
      synchronizedTransaction({
        nSelects = nSelects + 1
        if (Models.filter(_.userid === userId).filter(_.name === name).list.isEmpty) {
          nInserts = nInserts + 1
          Some((Models.map(m => (m.userid.get, m.name.get, m.filecontents.get, m.date.get, m.description, m.publink, m.title, m.tactic))
            returning Models.map(_._Id.get))
            .insert(userId, name, fileContents, date, description, publink, title, tactic))
        }
        else None
      })

    override def createProofForModel(modelId: Int, name: String, description: String, date: String): Int =
      synchronizedTransaction({
        nInserts = nInserts + 2
        val proofId =
          (Proofs.map(p => ( p.modelid.get, p.name.get, p.description.get, p.date.get, p.closed.get))
            returning Proofs.map(_._Id.get))
            .insert(modelId, name, description, date, 0)
        Tacticexecutions.map(te => te.proofid.get).insert(proofId)
        proofId
      })

    override def getModel(modelId: Int): ModelPOJO =
      synchronizedTransaction({
        nSelects = nSelects + 1
        val models =
          Models.filter(_._Id === modelId)
            .list
            .map(m => new ModelPOJO(
              m._Id.get, m.userid.get, blankOk(m.name), blankOk(m.date), m.filecontents.get, blankOk(m.description),
              blankOk(m.publink), blankOk(m.title), m.tactic, getNumProofs(m._Id.get)
            ))
        if (models.length < 1) throw new Exception("getModel type should be an Option")
        else if (models.length == 1) models.head
        else throw new Exception("Primary keys aren't unique in models table.")
      })

    override def deleteModel(modelId: Int): Boolean =
      synchronizedTransaction({
        Models.filter(_._Id === modelId).delete
        Proofs.filter(_.modelid === modelId).list.map(prf => deleteProof(prf._Id.get))
        true
      })

    override def getUsername(uid: String): String =
      uid

    private def optToString[T](o: Option[T]) = o match {
      case Some(x) => Some(x.toString)
      case None => None
    }

    override def getConfiguration(configName: String): ConfigurationPOJO =
      synchronizedTransaction({
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

    /** Creates a new execution and returns the new ID in tacticExecutions */
    override def createExecution(proofId: Int): Int =
      synchronizedTransaction({
        val executionId =
          (Tacticexecutions.map(te => te.proofid.get)
            returning Tacticexecutions.map(_._Id.get))
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
      synchronizedTransaction({
        val status = ExecutionStepStatus.toString(step.status)
        val steps =
          Executionsteps.map({case dbstep => (dbstep.executionid.get, dbstep.previousstep, dbstep.parentstep,
            dbstep.branchorder.get, dbstep.branchlabel.get, dbstep.alternativeorder.get, dbstep.status.get, dbstep.executableid.get,
            dbstep.inputprovableid, dbstep.resultprovableid, dbstep.localprovableid, dbstep.userexecuted.get, dbstep.childrenrecorded.get,
            dbstep.rulename.get)
          }) returning Executionsteps.map(es => es._Id.get)
        val stepId = steps
            .insert((step.executionId, step.previousStep, step.parentStep, branchOrder, branchLabel,
              step.alternativeOrder, status, step.executableId, step.inputProvableId, step.resultProvableId,
              step.localProvableId, step.userExecuted.toString, false.toString, step.ruleName))
        nInserts = nInserts + 1
        stepId
      })
    }

    override def addAlternative(alternativeTo: Int, inputProvable: Provable, trace:ExecutionTrace):Unit = {
      def get(stepId: Int) = {
        Executionsteps.filter(_._Id === stepId).list match {
          case Nil => throw new Exception("Execution step not found")
          case step :: _ => step
        }
      }
      val oldStep = get(alternativeTo)
      def addSteps(prev: Option[Int], globalProvable:Provable, steps:List[ExecutionStep]): Unit = {
        if (steps.nonEmpty) {
          val thisStep = steps.head
          val thisPOJO = get(thisStep.stepId)
          val localProvable = loadProvable(thisPOJO.localprovableid.get)
          val outputProvable = globalProvable(localProvable, thisStep.branch)
          val newStep = new ExecutionStepPOJO(None, oldStep.executionid.get, prev, None, Some(thisStep.branch),
            None, oldStep.alternativeorder.get + 1, ExecutionStepStatus.fromString(thisPOJO.status.get), thisPOJO.executableid.get,
            None, None, thisPOJO.localprovableid, thisPOJO.userexecuted.get.toBoolean, thisPOJO.rulename.get)
          val newId = addExecutionStep(newStep)
          addSteps(Some(newId), outputProvable, steps.tail)
        }
      }
      if(trace.steps.isEmpty) {
        // Insert a null tactic with a higher alternative order
        val nilExecutable = addBelleExpr(TactixLibrary.nil)
        val localConclusion = inputProvable.subgoals(0)
        // Generate a no-op local provable whose conclusion matches with the current state of the proof.
        val localProvable = Provable.startProof(localConclusion)
        val newLocalProvableID = serializeProvable(localProvable)
        val step = new ExecutionStepPOJO(None, oldStep.executionid.get, oldStep.previousstep, None, Some(0), None,
          oldStep.alternativeorder.get + 1, ExecutionStepStatus.Finished, nilExecutable, oldStep.inputprovableid,
          oldStep.inputprovableid, Some(newLocalProvableID), false, "nil")
        addExecutionStep(step)
      } else {
        addSteps(oldStep.previousstep, inputProvable, trace.steps)
      }
    }

    /** Adds a Bellerophon expression as an executable and returns the new executableId */
    override def addBelleExpr(expr: BelleExpr): Int =
      synchronizedTransaction({
        val executableId =
          (Executables.map({ case exe => (exe.scalatacticid, exe.belleexpr) })
            returning Executables.map(_._Id.get))
          .insert((None, Some(expr.prettyString)))
        nInserts = nInserts + 1
        executableId
      })

    private[SQLite] def createLemma(): Int = {
      synchronizedTransaction({
        (Lemmas.map(_.lemma) returning Lemmas.map(_._Id.get))
          .insert(None)
      })
    }

    private[SQLite] def updateLemma(lemmaId: Int, lemma:String): Unit = {
      synchronizedTransaction({
        Lemmas.filter(_._Id === lemmaId).map(_.lemma).update(Some(lemma))
      })
    }

    private[SQLite] def getLemma(lemmaId: Int): Option[String] = {
      getLemmas(List(lemmaId)) match {
        case Some(lemmas) => lemmas.headOption
        case None => None
      }
    }

    /** Allow retrieving lemmas in bulk to reduce the number of database queries */
    private[SQLite] def getLemmas(lemmaIds: List[Int]): Option[List[String]] = {
      synchronizedTransaction({
        val allLemmas = Lemmas.map{case row => (row._Id.get, row.lemma.get)}.list
        /** Build a map from the lemmas to avoid an O(m*n) search. Since this map contains the unparsed lemmas, it does
          * not incur the overhead of parsing every lemma in the database. */
        val lemmaMap =
          allLemmas.foldLeft(Map.empty[Int, String]){case (map, (id, lemma)) => map.+((id, lemma))}
        try {
          Some(lemmaIds.map(lemmaMap(_)))
        } catch {
          case _:Exception => None
        }
      })
    }

    private[SQLite] def deleteLemma(lemmaId: Int): Unit = {
      synchronizedTransaction({
        Lemmas.filter(_._Id === lemmaId).delete
      })
    }

    private[SQLite] def deleteAllLemmas(): Unit = {
      synchronizedTransaction({
        Lemmas.delete
      })
    }

    /** Stores a Provable in the database and returns its ID */
    override def serializeProvable(p: Provable): Int = {
      synchronizedTransaction({
        val lemma = Lemma(p, List(new ToolEvidence(List("input" -> p.prettyString, "output" -> "true"))))
        lemmaDB.add(lemma).toInt
      })
    }

    /** Returns the executable with ID executableId */
    override def getExecutable(executableId: Int): ExecutablePOJO = {
      getExecutables(List(executableId)).head
    }

    /** Allow retrieving executables in bulk to reduce the number of database queries. */
    def getExecutables(executableIds: List[Int]): List[ExecutablePOJO] =
      synchronizedTransaction({
        nSelects = nSelects + 1
        val executableMap =
          Executables.map(exe => (exe._Id.get, exe.scalatacticid, exe.belleexpr))
          .list
          .map{case (id, tacticid, expr) => (id, ExecutablePOJO(id, tacticid, expr))}
          .foldLeft(Map.empty[Int,ExecutablePOJO]){case (acc, (id, exe)) => acc.+((id, exe))}

        try {
          executableIds.map{case id => executableMap(id)}
        } catch {
          case _:Exception => throw new ProverException("getExecutable type should be an Option")
        }
      })

    /** Use escape hatch in prover core to create a new Provable */
    override def loadProvable(lemmaId: Int): Provable = {
      loadProvables(List(lemmaId)).head
    }

    def loadProvables(lemmaIds: List[Int]): List[Provable] = {
      lemmaDB.get(lemmaIds) match {
        case None => throw new Exception (" No lemma for one of these IDs: " + lemmaIds)
        case Some(lemmas) => lemmas.map(_.fact)
      }
    }

    /** Rerun all execution steps to generate a provable for the current state of the proof
      * Assumes the execution starts with a trivial provable (one subgoal, which is the same
      * as the conclusion)
      *
      * This is only for testing purposes. If you need the last provable of an execution,trace,
      * you should use getExecutionTrace(id).lastProvable
      * */
    private def regenerate(proofId: Int): Provable = {
      val trace = getExecutionTrace(proofId)
      val inputProvable = Provable.startProof(trace.conclusion)
      val initialProvable = Provable.startProof(inputProvable.conclusion)
      def run(p: Provable, t:BelleExpr): Provable =
        SequentialInterpreter(Nil)(t,BelleProvable(p)) match {
          case BelleProvable(pr, _) => pr
        }
      def loadTactic(id: Int): BelleExpr = BTacticParser(getExecutable(id).belleExpr.get).get
      trace.steps.foldLeft(initialProvable)({case (provable, currStep) =>
          run(provable, loadTactic(currStep.executableId))
        })
      initialProvable
    }

    /** Return a string describing each step in the current state of the proof.
      * As of this writing, callers only use the length of the list and not the
      * individual strings, thus the exact representation is currently unspecified. */
    private def describeProofSteps(proofId: Int): List[String] = {
      getTacticExecution(proofId) match {
        case Some(execution) => proofSteps(execution).map(_.toString)
        case None => List.empty
      }
    }

    override def addAgendaItem(proofId: Int, initialProofNode: Int, displayName:String): Int = {
      synchronizedTransaction({
        (Agendaitems.map({case item => (item.proofid.get, item.initialproofnode.get, item.displayname.get)})
          returning Agendaitems.map(_._Id.get))
          .insert(proofId, initialProofNode, displayName)
      })
    }

    override def updateAgendaItem(item:AgendaItemPOJO) = {
      synchronizedTransaction({
        Agendaitems.filter(_._Id === item.itemId)
          .map({case dbitem => (dbitem.proofid.get, dbitem.initialproofnode.get, dbitem.displayname.get)})
          .update((item.proofId, item.initialProofNode, item.displayName))
      })
    }

    override def agendaItemsForProof(proofId: Int): List[AgendaItemPOJO] = {
      synchronizedTransaction({
        Agendaitems.filter(_.proofid === proofId)
        .list
        .map({case item => AgendaItemPOJO(item._Id.get, item.proofid.get, item.initialproofnode.get, item.displayname.get)})
      })
    }

    override def getAgendaItem(proofId: Int, initialProofNode: Int): Option[AgendaItemPOJO] = {
      synchronizedTransaction({
        Agendaitems.filter{row => row.proofid === proofId && row.initialproofnode === initialProofNode}
          .list
          .map({case item => AgendaItemPOJO(item._Id.get, item.proofid.get, item.initialproofnode.get, item.displayname.get)})
          .headOption
      })
    }

    /** Adds a built-in tactic application using a set of parameters */
    override def addAppliedScalaTactic(scalaTacticId: Int, params: List[ParameterPOJO]): Int = {
      synchronizedTransaction({
        val executableId =
          (Executables.map({ case exe => ( exe.scalatacticid, exe.belleexpr)})
            returning Executables.map(_._Id.get))
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
      synchronizedTransaction({
        nSelects = nSelects + 1
        nUpdates = nUpdates + 1
        Executionsteps.filter(_._Id === executionStepId).map(_.status).update(Some(newStatus))
      })
    }


    def updateResultProvables(executionStepId: Int, provableId: Option[Int], localProvableId: Option[Int]): Unit = {
      synchronizedTransaction({
        nSelects = nSelects + 1
        nUpdates = nUpdates + 1
        Executionsteps
          .filter(_._Id === executionStepId)
          .map({row => (row.resultprovableid, row.localprovableid)})
          .update((provableId, localProvableId))
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
      loadProvable(provableId).conclusion
    }

    def printStats(): Unit = {
      println("Updates: " + nUpdates + " Inserts: " + nInserts + " Selects: " + nSelects)
    }

    def proofSteps(executionId: Int, status: Option[ExecutionStepStatus] = Some(ExecutionStepStatus.Finished)): List[ExecutionStepPOJO] = {
      synchronizedTransaction({
        def statusFilter(row: Executionsteps): Column[Option[Boolean]] = status match {
          case Some(s) => row.status === ExecutionStepStatus.toString(s)
          case None => Some(true)
        }
        var steps = Executionsteps.filter({case row => row.executionid === executionId && statusFilter(row)}).list
        var prevId: Option[Int] = None
        var revResult: List[ExecutionStepPOJO] = Nil
        /* The Executionsteps table may contain many alternate histories for the same execution. In order to reconstruct
        * the current state of the world, we must pick the most recent alternative at every opportunity.*/
        steps = steps.sortWith({case (x, y) => y.alternativeorder.get < x.alternativeorder.get})
        while(steps != Nil) {
          val (headSteps, tailSteps) = steps.partition({step => step.previousstep == prevId})
          if (headSteps == Nil)
            return revResult.reverse
          val head = headSteps.head
          revResult =
            new ExecutionStepPOJO(head._Id, head.executionid.get, head.previousstep, head.parentstep,
              head.branchorder, head.branchlabel, head.alternativeorder.get, ExecutionStepStatus.fromString(head.status.get),
              head.executableid.get, head.inputprovableid, head.resultprovableid, head.localprovableid, head.userexecuted.get.toBoolean,
              head.rulename.get)::revResult
          prevId = head._Id
          steps = tailSteps
        }
        revResult.reverse
      })
    }

    private def getProofConclusion(proofId: Int): Sequent = {
      val modelId = getProofInfo(proofId).modelId
      val model = getModel(modelId)
      KeYmaeraXProblemParser(model.keyFile) match {
        case fml:Formula => Sequent(collection.immutable.IndexedSeq(), collection.immutable.IndexedSeq(fml))
        case _ => throw new Exception("Failed to parse model for proof " + proofId + " model " + modelId)
      }
    }

    private def getTacticExecution(proofId: Int): Option[Int] =
      synchronizedTransaction({
          val executionIds =
            Tacticexecutions.filter(_.proofid === proofId)
              .list
              .map({ case row => row._Id.get })
          if (executionIds.length < 1) None
          else if (executionIds.length == 1) Some(executionIds.head)
          else throw new Exception("Primary keys aren't unique in executions table.")
        })

    private def zipTrace(executionSteps: List[ExecutionStepPOJO], executables: List[ExecutablePOJO], inputProvable:Provable, localProvables: List[Provable]): List[ExecutionStep] = {
      (executionSteps, executables, localProvables) match {
        case (step::steps, exe:: exes, localProvable::moreProvables) =>
          val output = inputProvable(localProvable, step.branchOrder.get)
          ExecutionStep(step.stepId.get, inputProvable, Some(localProvable), step.branchOrder.get, step.alternativeOrder, step.ruleName, step.executableId, step.userExecuted)  ::
            zipTrace(steps, exes, output, moreProvables)
        case (Nil, Nil, Nil) => Nil
        case _ => throw new ProverException("Bug in zipTrace")
      }
    }

    override def getExecutionSteps(executionId: Int, status: Option[ExecutionStepStatus]): List[ExecutionStepPOJO] = proofSteps(executionId, status)

    override def getExecutionTrace(proofId: Int): ExecutionTrace = {
      /* This method has proven itself to be a resource hog, so this implementation attempts to minimize the number of
         DB calls. */
      getTacticExecution(proofId) match {
        case Some(executionId) =>
          val steps = proofSteps(executionId)
          if (steps.isEmpty) {
            val conclusion = getProofConclusion(proofId)
            ExecutionTrace(proofId.toString, executionId.toString, conclusion, Nil)
          } else {
            val provableIds = steps.map { case step => step.localProvableId.get }
            val executableIds = steps.map { case step => step.executableId }
            val provables = loadProvables(provableIds)
            val conclusion = provables.head.conclusion
            val initProvable = Provable.startProof(conclusion)
            val executables = getExecutables(executableIds)
            val traceSteps = zipTrace(steps, executables, initProvable, provables)
            ExecutionTrace(proofId.toString, executionId.toString, conclusion, traceSteps)
          }
        case None =>
          val conclusion = getProofConclusion(proofId)
          //@todo is execution ID really unused so far?
          ExecutionTrace(proofId.toString, null, conclusion, Nil)
      }
    }

    override def getInvariants(modelId: Int): Map[Expression, Formula] = {
      val model = getModel(modelId)
      var invariants: Map[Expression, Formula] = Map.empty
      KeYmaeraXParser.setAnnotationListener{case (program, formula) =>
        invariants = invariants.+((program, formula))
      }
      KeYmaeraXProblemParser(model.keyFile)
      invariants
    }

  }
}