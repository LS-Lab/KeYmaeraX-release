/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.hydra

import java.io.FileOutputStream
import java.nio.channels.Channels

import _root_.edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary
import _root_.edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXProblemParser}
import _root_.edu.cmu.cs.ls.keymaerax.tools.ToolEvidence
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleProvable, SequentialInterpreter}
import _root_.edu.cmu.cs.ls.keymaerax.core.{Formula, Sequent, _}
import edu.cmu.cs.ls.keymaerax.lemma._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable.Nil

//import Tables.TacticonproofRow
import scala.slick.driver.SQLiteDriver.simple._
import scala.slick.jdbc.StaticQuery.interpolation

/**
  * In-memory database, e.g., for stepping into tactics.
  * @author Stefan Mitsch
  */
class InMemoryDB extends DBAbstraction {

  private val models: scala.collection.mutable.Map[Int, ModelPOJO] = scala.collection.mutable.Map()
  private val proofs: scala.collection.mutable.Map[Int, (ProvableSig, ProofPOJO)] = scala.collection.mutable.Map()
  //@note proofId = executionId
  private val executionSteps: scala.collection.mutable.Map[Int, ExecutionStepPOJO] = scala.collection.mutable.Map()
  private val executables: scala.collection.mutable.Map[Int, ExecutablePOJO] = scala.collection.mutable.Map()
  private val provables: scala.collection.mutable.Map[Int, ProvableSig] = scala.collection.mutable.Map()


  // Configuration and database setup and initialization and all DB communication

  override def getAllConfigurations: Set[ConfigurationPOJO] = ???

  override def getModelList(userId: String): List[ModelPOJO] = ???

  override def createUser(username: String, password: String): Unit = ???

  /**
    * Poorly named -- either update the config, or else insert an existing key.
    * But in Mongo it was just update, because of the nested documents thing.
    *
    * @param config
    */
  override def updateConfiguration(config: ConfigurationPOJO): Unit = ???

  //Proofs and Proof Nodes
  override def getProofInfo(proofId: Int): ProofPOJO = synchronized { proofs(proofId)._2 }

  // Users
  override def userExists(username: String): Boolean = ???

  override def getProofsForUser(userId: String): List[(ProofPOJO, String)] = ???

  override def checkPassword(username: String, password: String): Boolean = ???

  override def updateProofInfo(proof: ProofPOJO): Unit = {
    val (provable, _) = proofs(proof.proofId)
    proofs(proof.proofId) = (provable, proof)
  }

  //returns id of create object
  override def getProofsForModel(modelId: Int): List[ProofPOJO] = synchronized {
    proofs.values.map(_._2).filter(_.modelId == modelId).toList
  }

  def deleteExecution(executionId: Int): Boolean = synchronized {
    //@todo remove executionSteps by executionId
    true
  }

  override def deleteProof(proofId: Int): Boolean = synchronized {
    //@todo remove executionSteps
    proofs.remove(proofId)
    true
  }

  //Models
  override def createModel(userId: String, name: String, fileContents: String, date: String,
                           description: Option[String] = None, publink: Option[String] = None,
                           title: Option[String] = None, tactic: Option[String] = None): Option[Int] =
  synchronized {
    if (!models.values.exists(_.name == name)) {
      val modelId = models.keys.size
      models(modelId) = new ModelPOJO(modelId, userId, name, date, fileContents, description.getOrElse(""),
        publink.getOrElse(""), title.getOrElse(""), tactic, 0)
      Some(modelId)
    } else None
  }

  override def addModelTactic(modelId: String, fileContents: String): Option[Int] = ???

  override def createProofForModel(modelId: Int, name: String, description: String, date: String): Int = synchronized {
    val proofId = proofs.keys.size
    //@todo create Provable from model content
    proofs(proofId) = (null, new ProofPOJO(proofId, modelId, name, description, date, 0, closed=false))
    proofId
  }

  def createProof(provable: ProvableSig): Int = synchronized {
    val proofId = proofs.keys.size
    val provableId = provables.keys.size
    provables(provableId) = provable
    proofs(proofId) = (provable, new ProofPOJO(proofId, 0, "", "", "", 0, closed=false))
    proofId
  }

  override def getModel(modelId: Int): ModelPOJO = synchronized { models(modelId) }

  override def deleteModel(modelId: Int): Boolean = synchronized {
    //@todo delete proofs
    models.remove(modelId)
    true
  }

  override def getConfiguration(configName: String): ConfigurationPOJO = ???

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
  override def createExecution(proofId: Int): Int = 0

  /** Deletes a provable and all associated sequents / formulas */
  override def deleteProvable(provableId: Int): Boolean = ???

  /**
    * Adds an execution step to an existing execution
    *
    * @note Implementations should enforce additional invarants -- never insert when branches or alt orderings overlap.
    */
  override def addExecutionStep(step: ExecutionStepPOJO): Int = synchronized {
    val stepId = executionSteps.keys.size
    executionSteps(stepId) = step
    stepId
  }

  override def addAlternative(alternativeTo: Int, inputProvable: ProvableSig, trace:ExecutionTrace): Unit = ???

  /** Adds a Bellerophon expression as an executable and returns the new executableId */
  override def addBelleExpr(expr: BelleExpr): Int = synchronized {
    val executableId = executables.keys.size
    executables(executableId) = new ExecutablePOJO(executableId, BellePrettyPrinter(expr))
    executableId
  }

  /** Stores a Provable in the database and returns its ID */
  override def createProvable(p: ProvableSig): Int = synchronized {
    val provableId = provables.keys.size
    provables(provableId) = p
    provableId
  }

  /** Returns the executable with ID executableId */
  override def getExecutable(executableId: Int): ExecutablePOJO = {
    getExecutables(List(executableId)).head
  }

  /** Allow retrieving executables in bulk to reduce the number of database queries. */
  def getExecutables(executableIds: List[Int]): List[ExecutablePOJO] = synchronized {
    executables.filterKeys(executableIds.contains).values.toList.sortBy(_.executableId)
  }

  /** Use escape hatch in prover core to create a new Provable */
  override def getProvable(lemmaId: Int): ProvablePOJO = {
    loadProvables(List(lemmaId)).head
  }

  def loadProvables(lemmaIds: List[Int]): List[ProvablePOJO] = provables.filterKeys(lemmaIds.contains).
    map({ case (k, v) => ProvablePOJO(k, v)}).toList.sortBy(_.provableId)

  override def addAgendaItem(proofId: Int, initialProofNode: Int, displayName:String): Int = ???

  override def updateAgendaItem(item:AgendaItemPOJO) = ???

  override def agendaItemsForProof(proofId: Int): List[AgendaItemPOJO] = ???

  override def getAgendaItem(proofId: Int, initialProofNode: Int): Option[AgendaItemPOJO] = ???

  /** Updates an executable step */
  override def updateExecutionStep(executionStepId: Int, step: ExecutionStepPOJO): Unit = synchronized {
    executionSteps(executionStepId) = step
  }

  def printStats(): Unit = ???

  def proofSteps(executionId: Int): List[ExecutionStepPOJO] = synchronized {
    /* The Executionsteps table may contain many alternate histories for the same execution. In order to reconstruct
     * the current state of the world, we must pick the most recent alternative at every opportunity.*/
    var steps = executionSteps.filter({case (k, v) =>
      v.executionId == executionId && v.status == ExecutionStepStatus.Finished}).values.toList.
      sortBy(_.alternativeOrder).reverse
    var prevId: Option[Int] = None
    var revResult: List[ExecutionStepPOJO] = Nil
    while(steps != Nil) {
      val (headSteps, tailSteps) = steps.partition(_.previousStep == prevId)
      if (headSteps == Nil)
        return revResult.reverse
      val head = headSteps.head
      revResult = head :: revResult
      prevId = head.stepId
      steps = tailSteps
    }
    revResult.reverse
  }

  private def getProofConclusion(proofId: Int): Sequent = proofs(proofId)._1.conclusion

  private def getTacticExecution(proofId: Int): Option[Int] = synchronized { Some(proofId) }

  private def zipTrace(executionSteps: List[ExecutionStepPOJO], executables: List[ExecutablePOJO], inputProvable:ProvableSig, localProvables: List[ProvableSig]): List[ExecutionStep] = {
    (executionSteps, executables, localProvables) match {
      case (step::steps, exe:: exes, localProvable::moreProvables) =>
        val output = inputProvable(localProvable, step.branchOrder.get)
        ExecutionStep(step.stepId.get, step.executionId, inputProvable, Some(localProvable), step.branchOrder.get, step.alternativeOrder, step.ruleName, step.executableId, step.userExecuted)  ::
          zipTrace(steps, exes, output, moreProvables)
      case (Nil, Nil, Nil) => Nil
      case _ => throw new ProverException("Bug in zipTrace")
    }
  }

  override def getExecutionSteps(executionId: Int): List[ExecutionStepPOJO] = proofSteps(executionId)

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
          val provableIds = steps.map(_.localProvableId.get)
          val executableIds = steps.map(_.executableId)
          val provables = loadProvables(provableIds).map(_.provable)
          val conclusion = provables.head.conclusion
          val initProvable = ProvableSig.startProof(conclusion)
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
    //@todo
//    val model = getModel(modelId)
//    var invariants: Map[Expression, Formula] = Map.empty
//    KeYmaeraXParser.setAnnotationListener{case (program, formula) =>
//      invariants = invariants.+((program, formula))
//    }
//    KeYmaeraXProblemParser.parseAsProblemOrFormula(model.keyFile)
//    invariants
    Map.empty
  }

  /** Ensures any changes which might currently reside in auxilliary storage have been synced to main storage. */
  override def syncDatabase(): Unit = ???

  //Proofs and Proof Nodes
  override def isProofClosed(proofId: Int): Boolean = ???
}