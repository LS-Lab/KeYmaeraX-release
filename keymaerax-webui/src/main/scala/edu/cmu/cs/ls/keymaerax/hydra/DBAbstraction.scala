/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.hydra

import _root_.edu.cmu.cs.ls.keymaerax.core.{Expression, Formula}

import java.io.File

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.hydra.ExecutionStepStatus.ExecutionStepStatus

import scala.collection.immutable.Nil

//Global setting:
object DBAbstractionObj {
  def defaultDatabase = SQLite.ProdDB //this needs to be a def and not a val because DBAbstractionObj is initialized in SQLite.
  def testDatabase = SQLite.TestDB
  private def getLocation(isTest: Boolean): String = {
    val dirname = ".keymaerax"
    val filename = if (isTest) "testDB.sqlite" else "keymaerax.sqlite"
    new File(
      System.getProperty("user.home") + File.separator + dirname
    ).mkdirs()
    val file = new File(System.getProperty("user.home") + File.separator +
      dirname + File.separator + filename)
    file.getCanonicalPath
  }

  val dblocation: String = getLocation(isTest=false)
  println(dblocation)
  val testLocation: String = getLocation(isTest=true)
}

class ConfigurationPOJO(val name: String, val config: Map[String,String])

/** A tutorial/case study example. */
class ExamplePOJO(val id: Int, val title: String, val description: String, val infoUrl: String, val url: String,
                  val imageUrl: String, val level: Int)

/**
 * Data object for models.
  *
  * @param modelId Identifies the model.
 * @param userId Identifies the user.
 * @param name The name of the model.
 * @param date The creation date.
 * @param keyFile The model file content.
 * @param description The description of the model.
 * @param pubLink Link to additional information (paper) on the model.
 */
class ModelPOJO(val modelId:Int, val userId:String, val name:String, val date:String, val keyFile:String,
                val description:String, val pubLink:String, val title:String, val tactic : Option[String],
                val numProofs: Int, val temporary: Boolean) //the other guys on this linke should also be optional.

/**
  * Data object for users.
  *
  * @param userName Identifies the user.
  * @param level The user's learner level.
  */
class UserPOJO(val userName: String, val level: Int)


/**
 * Data object for proofs. A proof
  *
  * @param proofId Identifies the proof.
  * @param modelId Identifies the model; if defined, model formula must agree with provable's conclusion
  * @param name The proof name.
  * @param description A proof description.
  * @param date The creation date.
  * @param stepCount The number of proof steps in the proof.
  * @param closed Indicates whether the proof is closed (finished proof) or not (partial proof).
  * @param provableId Refers to a provable whose conclusion to prove.
  * @param temporary Indicates whether or not the proof is temporary.
 */
class ProofPOJO(val proofId:Int, val modelId: Option[Int], val name:String, val description:String,
                val date:String, val stepCount : Int, val closed : Boolean, val provableId: Option[Int],
                val temporary: Boolean = false) {
  assert(modelId.isDefined || provableId.isDefined, "Require either model or provable")
}

case class ProvablePOJO(provableId: Int, provable:ProvableSig)

case class SequentPOJO(sequentId: Int, provableId: Int)

case class SequentFormulaPOJO(sequentFormulaId: Int, sequentId: Int, isAnte: Boolean, index: Int, formulaStr: String)

case class AgendaItemPOJO(itemId: Int, proofId: Int, initialProofNode: ProofTreeNodeId, displayName: String)

/* See schema for descriptions */
object ExecutionStepStatus extends Enumeration {
  type ExecutionStepStatus = Value
  val Prepared, Running, Finished, Aborted, Error, DependsOnChildren = Value

  def fromString(s : String): ExecutionStepStatus = s match {
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

case class TacticExecutionPOJO(executionId: Int, proofId: Int)

case class ExecutionStepPOJO(stepId: Option[Int], executionId: Int,
                             previousStep: Option[Int],
                             branchOrder: Int,
                             status: ExecutionStepStatus,
                             executableId: Int,
                             inputProvableId: Option[Int],
                             resultProvableId: Option[Int],
                             localProvableId: Option[Int],
                             userExecuted: Boolean,
                             ruleName: String,
                             numSubgoals: Int,
                             numOpenSubgoals: Int)
{

}

/** A proof step in a proof execution trace, can be represented as a node in a proof tree. */
case class ExecutionStep(stepId: Int, prevStepId: Option[Int], executionId: Int,
                         localProvableLoader: () => ProvableSig, branch: Int, subgoalsCount: Int, openSubgoalsCount: Int,
                         successorIds: List[Int],
                         rule: String, executableId: Int, isUserExecuted: Boolean = true) {

  /** Triggers a database call if step was loaded without provables. */
  def local: ProvableSig = localProvableLoader()

}

case class ExecutionTrace(proofId: String, executionId: String, steps: List[ExecutionStep]) {
  //@note expensive assert
  assert(isTraceExecutable(steps), "Trace steps not ordered in descending branches")

  def isTraceExecutable(steps: List[ExecutionStep]): Boolean = steps match {
    case Nil => true
    case step::tail => tail.filter(_.prevStepId == step.prevStepId).forall(_.branch < step.branch) && isTraceExecutable(tail)
  }

  def branch: Option[Int] = steps.lastOption.map(_.branch)

  def lastStepId:Option[Int] = steps.lastOption.map(_.stepId)
}

case class ExecutablePOJO(executableId: Int, belleExpr:String)

/**
 * Proof database
 */
trait DBAbstraction {
  /**
    * Initializes a new database.
    */
  def cleanup(): Unit

  /** Ensures any changes which might currently reside in auxilliary storage have been synced to main storage. */
  def syncDatabase(): Unit

  // Configuration
  def getAllConfigurations: Set[ConfigurationPOJO]

  def getConfiguration(configName: String): ConfigurationPOJO

  def updateConfiguration(config: ConfigurationPOJO)

  // Users
  def userExists(username: String): Boolean

  def createUser(username: String, password: String, mode: String): Unit

  def getUser(username: String): UserPOJO

  def checkPassword(username: String, password: String): Boolean

  def getProofsForUser(userId: String): List[(ProofPOJO, String)]

  def openProofs(userId: String): List[ProofPOJO] =
    getProofsForUser(userId).map(_._1).filter(!_.closed)

  //Models
  def createModel(userId: String, name: String, fileContents: String, date: String,
                  description: Option[String] = None, publink: Option[String] = None,
                  title: Option[String] = None, tactic: Option[String] = None): Option[Int]

  def getModel(modelId: Int): ModelPOJO

  /** Deletes this model and all associated proofs. */
  def deleteModel(modelId: Int): Boolean

  def getModel(modelId: String): ModelPOJO = getModel(modelId.toInt)

  def getModelList(userId: String): List[ModelPOJO]

  def getInvariants(modelId: Int): Map[Expression, Formula]

  //Proofs of models
  def createProofForModel(modelId: Int, name: String, description: String, date: String): Int

  // all create functions return ID of created object
  def createProofForModel(modelId: String, name: String, description: String, date: String): String =
    createProofForModel(modelId.toInt, name, description, date).toString

  /** Create a temporary proof without model, starting from 'provable'. */
  def createProof(provable: ProvableSig): Int

  def getProofsForModel(modelId: Int): List[ProofPOJO]

  def getProofsForModel(modelId: String): List[ProofPOJO] = getProofsForModel(modelId.toInt)

  def deleteProof(proofId: Int) : Boolean

  //Proofs and Proof Nodes
  def isProofClosed(proofId: Int): Boolean

  def getProofInfo(proofId: Int): ProofPOJO

  def getProofInfo(proofId: String): ProofPOJO = getProofInfo(proofId.toInt)

  def updateProofInfo(proof: ProofPOJO)

  def updateProofName(proofId: Int, name: String): Unit = {
    val info = getProofInfo(proofId)
    updateProofInfo(new ProofPOJO(proofId, info.modelId, name, info.description, info.date,
      info.stepCount, info.closed, info.provableId, info.temporary))
  }

  def updateProofName(proofId: String, name: String): Unit = updateProofName(proofId.toInt, name)

  def updateModel(modelId: Int, name: String, title: Option[String], description: Option[String]): Unit

  def addAgendaItem(proofId: Int, initialProofNode: ProofTreeNodeId, displayName:String): Int

  def getAgendaItem(proofId: Int, initialProofNode: ProofTreeNodeId): Option[AgendaItemPOJO]

  def updateAgendaItem(item:AgendaItemPOJO): Unit

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
    * @note Implementations should enforce additional invarants -- never insert when branches or alt orderings overlap.
    */
  def addExecutionStep(step: ExecutionStepPOJO): Int

  /** Truncate the execution trace at the beginning of alternativeTo and replace it with trace. */
  def addAlternative(alternativeTo: Int, inputProvable: ProvableSig, trace:ExecutionTrace)

  /** Return the sequence of steps that led to the current state of the proof. Loading a trace with provables is slow. */
  def getExecutionTrace(proofID: Int, withProvables: Boolean=true): ExecutionTrace

  /** Return a list of all finished execution steps in the current history of the execution, in the order in which they
    * occurred.
    * @note For most purposes, getExecutionTrace is more convenient, but slower. */
  def getExecutionSteps(executionId: Int) : List[ExecutionStepPOJO]

  /** Returns the first step of the proof */
  def getFirstExecutionStep(proofId: Int) : Option[ExecutionStepPOJO]

  /** Returns a list of steps that do not have successors for each of their subgoals.
    * Along with each step, it lists the step's subgoals that are actually closed. */
  def getPlainOpenSteps(proofId: Int): List[(ExecutionStepPOJO,List[Int])]

  /** Returns the execution step with id `stepId` of proof `proofId` in plain database form. */
  def getPlainExecutionStep(proofId: Int, stepId: Int): Option[ExecutionStepPOJO]

  /** Returns the successors of the execution step with id `stepId` of proof `proofId` in plain database form. */
  def getPlainStepSuccessors(proofId: Int, prevStepId: Int, branchOrder: Int): List[ExecutionStepPOJO]

  /** Returns the execution step with id `stepId` of proof `proofId` with all provables etc. filled in. */
  def getExecutionStep(proofId: Int, stepId: Int): Option[ExecutionStep]

  /** Returns the `subgoal` of execution step `stepId` of proof `proofId`; proof conclusion if both None. */
  def getStepProvable(proofId: Int, stepId: Option[Int], subgoal: Option[Int]): Option[ProvableSig]

  /** Update existing execution step. */
  def updateExecutionStep(executionStepId: Int, step:ExecutionStepPOJO): Unit

  /** Delete an execution step. */
  def deleteExecutionStep(proofId: Int, stepId: Int): Unit

  /////////////////////
  /** Adds a bellerophon expression as an executable and returns the new executableId */
  def addBelleExpr(expr: BelleExpr): Int

  /** Returns the executable with ID executableId */
  def getExecutable(executableId: Int): ExecutablePOJO
}
