/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra

import _root_.edu.cmu.cs.ls.keymaerax.core.{Expression, Formula}

import java.io.File
import edu.cmu.cs.ls.keymaerax.{Configuration, Logging}
import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.hydra.ExecutionStepStatus.ExecutionStepStatus
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, Declaration, Region}

import scala.collection.immutable.Nil

//Global setting:
object DBAbstractionObj extends Logging {
  def defaultDatabase: SQLite.SQLiteDB =
    SQLite.ProdDB // this needs to be a def and not a val because DBAbstractionObj is initialized in SQLite.
  def testDatabase: SQLite.SQLiteDB = SQLite.TestDB
  private def getLocation(isTest: Boolean): String = {
    new File(Configuration.path(if (isTest) Configuration.Keys.TEST_DB_PATH else Configuration.Keys.DB_PATH))
      .getCanonicalPath
  }

  val dblocation: String = getLocation(isTest = false)
  logger.info("Using database " + dblocation)
  val testLocation: String = getLocation(isTest = true)
}

class ConfigurationPOJO(val name: String, val config: Map[String, String])

/** A tutorial/case study example. */
case class ExamplePOJO(
    id: Int,
    title: String,
    description: String,
    infoUrl: String,
    url: String,
    imageUrl: String,
    level: Int,
)

/** A text template with optional region to select and set the cursor to on display. */
case class TemplatePOJO(
    title: String,
    description: String,
    text: String,
    selectRange: Option[Region],
    imageUrl: Option[String],
)

/**
 * Data object for models.
 *
 * @param modelId
 *   Identifies the model.
 * @param userId
 *   Identifies the user.
 * @param name
 *   The name of the model.
 * @param date
 *   The creation date.
 * @param keyFile
 *   The model file content.
 * @param description
 *   The description of the model.
 * @param pubLink
 *   Link to additional information (paper) on the model.
 */
case class ModelPOJO(
    modelId: Int,
    userId: String,
    name: String,
    date: String,
    keyFile: String,
    description: String,
    pubLink: String,
    title: String,
    tactic: Option[String],
    // the other guys on this linke should also be optional.
    numAllProofSteps: Int,
    temporary: Boolean,
) {

  /** Returns the function, predicate, program symbol definitions of this model. */
  lazy val defs: Declaration = ArchiveParser(keyFile) match {
    case e :: Nil => e.defs
    case _ => Declaration(Map.empty)
  }

}

/**
 * Data object for users.
 *
 * @param userName
 *   Identifies the user.
 * @param level
 *   The user's learner level.
 */
class UserPOJO(val userName: String, val level: Int)

/**
 * Data object for proofs.
 *
 * @param proofId
 *   Identifies the proof.
 * @param modelId
 *   Identifies the model; if defined, model formula must agree with provable's conclusion
 * @param name
 *   The proof name.
 * @param description
 *   A proof description.
 * @param date
 *   The creation date.
 * @param stepCount
 *   The number of proof steps in the proof.
 * @param closed
 *   Indicates whether the proof is closed (finished proof) or not (partial proof).
 * @param provableId
 *   Refers to a provable whose conclusion to prove.
 * @param temporary
 *   Indicates whether or not the proof is temporary.
 * @param tactic
 *   The tactic to recreate the proof.
 */
case class ProofPOJO(
    proofId: Int,
    modelId: Option[Int],
    name: String,
    description: String,
    date: String,
    stepCount: Int,
    closed: Boolean,
    provableId: Option[Int],
    temporary: Boolean = false,
    tactic: Option[String],
) {
  assert(modelId.isDefined || provableId.isDefined, "Require either model or provable")

  /** Returns the function, predicate, program symbol definitions of the model associated with this proof. */
  def defs(db: DBAbstraction): Declaration = modelId.map(db.getModel).map(_.defs).getOrElse(Declaration(Map.empty))

}

case class ProvablePOJO(provableId: Int, provable: ProvableSig)

case class AgendaItemPOJO(itemId: Int, proofId: Int, initialProofNode: ProofTreeNodeId, displayName: String)

/* See schema for descriptions */
object ExecutionStepStatus extends Enumeration {
  type ExecutionStepStatus = Value
  val Prepared, Running, Finished, Aborted, Error, DependsOnChildren = Value

  def fromString(s: String): ExecutionStepStatus = s match {
    case "Prepared" => Prepared
    case "Running" => Running
    case "Finished" => Finished
    case "Aborted" => Aborted
    case "Error" => Error
    case "DependsOnChildren" => DependsOnChildren
    case _ => throw new Exception("Status " + s + " not in enum.")
  }

  def toString(status: ExecutionStepStatus): String = status match {
    case Prepared => "Prepared"
    case Running => "Running"
    case Finished => "Finished"
    case Aborted => "Aborted"
    case Error => "Error"
    case DependsOnChildren => "DependsOnChildren"
  }
}

case class ExecutionStepPOJO(
    stepId: Option[Int],
    executionId: Int,
    previousStep: Option[Int],
    branchOrder: Int,
    status: ExecutionStepStatus,
    executableId: Int,
    inputProvableId: Option[Int],
    resultProvableId: Option[Int],
    localProvableId: Option[Int],
    userExecuted: Boolean,
    ruleName: String,
    branchLabel: Option[String],
    numSubgoals: Int,
    numOpenSubgoals: Int,
) {}

/** A proof step in a proof execution trace, can be represented as a node in a proof tree. */
case class ExecutionStep(
    stepId: Int,
    prevStepId: Option[Int],
    executionId: Int,
    localProvableLoader: () => ProvableSig,
    branch: Int,
    subgoalsCount: Int,
    openSubgoalsCount: Int,
    successorIds: List[Int],
    rule: String,
    executableId: Int,
    isUserExecuted: Boolean = true,
) {

  /** Triggers a database call if step was loaded without provables. */
  def local: ProvableSig = localProvableLoader()

}

case class ExecutionTrace(proofId: String, executionId: String, steps: List[ExecutionStep]) {
  // @note expensive assert
  private val orderViolationStep = findOutOfOrderBranchStep(steps)
  assert(
    orderViolationStep.isEmpty,
    "Trace steps not ordered in descending branches:" + " branch " + orderViolationStep.get._1.branch + " of step " +
      orderViolationStep.get._1.stepId + " (" + orderViolationStep.get._1.rule + ")" + " is not less than branch " +
      orderViolationStep.get._2.branch + " of its sibling " + orderViolationStep.get._2.stepId + " (" +
      orderViolationStep.get._2.rule + ")" +
      (if (orderViolationStep.get._1.prevStepId.isDefined) " on parent " + orderViolationStep.get._1.prevStepId.get +
         " (" + steps.find(_.stepId == orderViolationStep.get._1.prevStepId.get).map(_.rule).getOrElse("unknown") + ")"
       else ""),
  )

  /** Finds the first step whose branch is out of order (higher than its predecessor's branch) */
  def findOutOfOrderBranchStep(steps: List[ExecutionStep]): Option[(ExecutionStep, ExecutionStep)] = steps match {
    case Nil => None
    // .orElse(findOutOfOrderBranchStep(tail))
    case step :: tail => tail.filter(_.prevStepId == step.prevStepId).find(_.branch >= step.branch) match {
        case None => findOutOfOrderBranchStep(tail)
        case Some(s) => Some(s -> step)
      }
  }

  def branch: Option[Int] = steps.lastOption.map(_.branch)

  def lastStepId: Option[Int] = steps.lastOption.map(_.stepId)
}

case class ExecutablePOJO(executableId: Int, belleExpr: String)

/** Proof database */
trait DBAbstraction {

  /** Initializes a new database. */
  def cleanup(): Unit

  /** Ensures any changes which might currently reside in auxilliary storage have been synced to main storage. */
  def syncDatabase(): Unit

  // Configuration
  def getAllConfigurations: Set[ConfigurationPOJO]

  def getConfiguration(configName: String): ConfigurationPOJO

  def updateConfiguration(config: ConfigurationPOJO): Unit

  // Users
  def userExists(username: String): Boolean

  /** Creates a new user, identified by the unique `username` with `password`. The user belongs to group `group`. */
  def createUser(username: String, password: String, group: String): Unit

  /** Returns the user identified by `username`, if any. */
  def getUser(username: String): Option[UserPOJO]

  /** Returns all temporary users (group 3). */
  def getTempUsers: List[UserPOJO]

  def checkPassword(username: String, password: String): Boolean

  def getProofsForUser(userId: String): List[(ProofPOJO, String)]

  /** Indicates whether or not the user `userId` owns the proof `proofId`. */
  def userOwnsProof(userId: String, proofId: String): Boolean

  def openProofs(userId: String): List[ProofPOJO] = getProofsForUser(userId).map(_._1).filter(!_.closed)

  // Models
  /** Returns a unique model name by appending an index, if `modelName` already exists. */
  def getUniqueModelName(userId: String, modelName: String): String

  /**
   * Creates a new model in the database if `name` does not exist yet. Returns the ID of the created model. Otherwise
   * (if the model name is used already) returns None and the database is unmodified.
   */
  def createModel(
      userId: String,
      name: String,
      fileContents: String,
      date: String,
      description: Option[String] = None,
      publink: Option[String] = None,
      title: Option[String] = None,
      tactic: Option[String] = None,
  ): Option[Int]

  def getModel(modelId: Int): ModelPOJO

  /** Deletes this model and all associated proofs. */
  def deleteModel(modelId: Int): Boolean

  def getModel(modelId: String): ModelPOJO = getModel(modelId.toInt)

  def getModelList(userId: String): List[ModelPOJO]

  def getInvariants(modelId: Int): Map[Expression, Formula]

  // Proofs of models
  def createProofForModel(modelId: Int, name: String, description: String, date: String, tactic: Option[String]): Int

  // all create functions return ID of created object
  def createProofForModel(
      modelId: String,
      name: String,
      description: String,
      date: String,
      tactic: Option[String],
  ): String = createProofForModel(modelId.toInt, name, description, date, tactic).toString

  /** Create a temporary proof without model, starting from 'provable'. */
  def createProof(provable: ProvableSig): Int

  def getProofsForModel(modelId: Int): List[ProofPOJO]

  def getProofsForModel(modelId: String): List[ProofPOJO] = getProofsForModel(modelId.toInt)

  /** Deletes the recorded proof steps, but keeps the proof and its tactic. Returns the number of deleted steps. */
  def deleteProofSteps(proofId: Int): Int

  /** Deletes the proof. */
  def deleteProof(proofId: Int): Boolean

  // Proofs and Proof Nodes
  def isProofClosed(proofId: Int): Boolean

  def proofExists(proofId: Int): Boolean

  def getProofInfo(proofId: Int): ProofPOJO

  def getProofInfo(proofId: String): ProofPOJO = getProofInfo(proofId.toInt)

  def updateProofInfo(proof: ProofPOJO): Unit

  def updateProofName(proofId: Int, name: String): Unit = {
    val info = getProofInfo(proofId)
    updateProofInfo(new ProofPOJO(
      proofId,
      info.modelId,
      name,
      info.description,
      info.date,
      info.stepCount,
      info.closed,
      info.provableId,
      info.temporary,
      info.tactic,
    ))
  }

  def updateProofName(proofId: String, name: String): Unit = updateProofName(proofId.toInt, name)

  def updateModel(
      modelId: Int,
      name: String,
      title: Option[String],
      description: Option[String],
      content: Option[String],
      tactic: Option[String],
  ): Unit

  def addAgendaItem(proofId: Int, initialProofNode: ProofTreeNodeId, displayName: String): Int

  def getAgendaItem(proofId: Int, initialProofNode: ProofTreeNodeId): Option[AgendaItemPOJO]

  def updateAgendaItem(item: AgendaItemPOJO): Unit

  def agendaItemsForProof(proofId: Int): List[AgendaItemPOJO]

  // Tactics
  /** Stores a Provable in the database and returns its ID */
  def createProvable(p: ProvableSig): Int

  /** Reconstruct a stored Provable */
  def getProvable(provableId: Int): ProvablePOJO

  /** Deletes a provable and all associated sequents / formulas */
  def deleteProvable(provableId: Int): Boolean

  /** Adds a tactic script to the model */
  def addModelTactic(modelId: String, tactic: String): Option[Int]

  /////////////////////

  /**
   * Adds an execution step to an existing execution
   *
   * @note
   *   Implementations should enforce additional invariants -- never insert when branches or alt orderings overlap.
   */
  def addExecutionStep(step: ExecutionStepPOJO): Int

  /** Truncate the execution trace at the beginning of alternativeTo and replace it with trace. */
  def addAlternative(alternativeTo: Int, inputProvable: ProvableSig, trace: ExecutionTrace): Unit

  /**
   * Return the sequence of steps that led to the current state of the proof. Loading a trace with provables is slow.
   */
  def getExecutionTrace(proofID: Int, withProvables: Boolean = true): ExecutionTrace

  /**
   * Return a list of all finished execution steps in the current history of the execution, in the order in which they
   * occurred.
   * @note
   *   For most purposes, getExecutionTrace is more convenient, but slower.
   */
  def getExecutionSteps(executionId: Int): List[ExecutionStepPOJO]

  /** Returns the first step of the proof */
  def getFirstExecutionStep(proofId: Int): Option[ExecutionStepPOJO]

  /**
   * Returns a list of steps that do not have successors for each of their subgoals (excludes steps that have no
   * subgoals or all subgoals closed). Along with each step, it lists the step's subgoals that are actually closed.
   */
  def getPlainOpenSteps(proofId: Int): List[(ExecutionStepPOJO, List[Int])]

  /**
   * Returns the leaf steps of the proof regardless of whether open or closed. Along with each step, it lists the step's
   * subgoals that are actually closed.
   */
  def getPlainLeafSteps(proofId: Int): List[(ExecutionStepPOJO, List[Int])]

  /** Returns the execution step with id `stepId` of proof `proofId` in plain database form. */
  def getPlainExecutionStep(proofId: Int, stepId: Int): Option[ExecutionStepPOJO]

  /** Returns the successors of the execution step with id `stepId` of proof `proofId` in plain database form. */
  def getPlainStepSuccessors(proofId: Int, prevStepId: Int, branchOrder: Int): List[ExecutionStepPOJO]

  /** Returns the execution step with id `stepId` of proof `proofId` with all provables etc. filled in. */
  def getExecutionStep(proofId: Int, stepId: Int): Option[ExecutionStep]

  /** Returns the `subgoal` of execution step `stepId` of proof `proofId`; proof conclusion if both None. */
  def getStepProvable(proofId: Int, stepId: Option[Int], subgoal: Option[Int]): Option[ProvableSig]

  /** Update existing execution step. */
  def updateExecutionStep(executionStepId: Int, step: ExecutionStepPOJO): Unit

  /** Delete an execution step. */
  def deleteExecutionStep(proofId: Int, stepId: Int): Unit

  /////////////////////

  /** Adds a bellerophon expression as an executable and returns the new executableId */
  def addBelleExpr(expr: BelleExpr): Int

  /** Returns the executable with ID executableId */
  def getExecutable(executableId: Int): ExecutablePOJO
}
