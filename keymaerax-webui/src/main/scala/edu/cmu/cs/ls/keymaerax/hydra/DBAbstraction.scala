/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.hydra

import java.nio.channels.Channels

import _root_.edu.cmu.cs.ls.keymaerax.core.{Expression, Provable, Formula, Sequent}

import java.io.File
import java.io.FileOutputStream

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.core.{Sequent, Provable}
import edu.cmu.cs.ls.keymaerax.hydra.ExecutionStepStatus.ExecutionStepStatus

import scala.collection.immutable.Nil
import scala.io.Source
import spray.json.DefaultJsonProtocol._

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
  val testLocation = getLocation(isTest=true)
}

class ConfigurationPOJO(val name: String, val config: Map[String,String])

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
                val description:String, val pubLink:String, val title:String, val tactic : Option[String], val numProofs: Int) //the other guys on this linke should also be optional.

/**
 * Data object for proofs. A proof
  *
  * @param proofId Identifies the proof.
 * @param modelId Identifies the model.
 * @param name The proof name.
 * @param description A proof description.
 * @param date The creation date.
 * @param stepCount The number of proof steps in the proof.
 * @param closed Indicates whether the proof is closed (finished proof) or not (partial proof).
 */
class ProofPOJO(val proofId:Int, val modelId:Int, val name:String, val description:String,
                val date:String, val stepCount : Int, val closed : Boolean)

case class ProvablePOJO(provableId: Int, provable:Provable)

case class SequentPOJO(sequentId: Int, provableId: Int)

case class SequentFormulaPOJO(sequentFormulaId: Int, sequentId: Int, isAnte: Boolean, index: Int, formulaStr: String)

case class AgendaItemPOJO(itemId: Int, proofId: Int, initialProofNode:Int, displayName: String)

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
                             previousStep: Option[Int], parentStep: Option[Int],
                             branchOrder: Option[Int],
                             branchLabel: Option[String],
                             alternativeOrder: Int,
                             status: ExecutionStepStatus,
                             executableId: Int,
                             inputProvableId: Option[Int],
                             resultProvableId: Option[Int],
                             localProvableId: Option[Int],
                             userExecuted: Boolean,
                             ruleName: String)
{
  require(branchOrder.isEmpty != branchLabel.isEmpty) //also schema constraint
}

/* User-friendly representation for execution traces */
case class ExecutionStep(stepId: Int, executionId: Int, input:Provable, local:Option[Provable], branch:Int, alternativeOrder:Int, rule:String, executableId: Int, isUserExecuted: Boolean = true) {
  def output: Option[Provable] = local.map{case localProvable => input(localProvable, branch)}
}

case class ExecutionTrace(proofId: String, executionId: String, conclusion: Sequent, steps:List[ExecutionStep]) {
  def branch = steps.lastOption.map{case step => step.branch}

  def alternativeOrder =
    steps match {
      case Nil => 0
      case _ => steps.last.alternativeOrder
    }

  def lastStepId:Option[Int] = {
    steps.lastOption.map{case step => step.stepId}
  }

  def lastProvable:Provable = steps.lastOption.flatMap(_.output).getOrElse(Provable.startProof(conclusion))
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

  def createUser(username: String, password: String): Unit

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

  def getProofsForModel(modelId: Int): List[ProofPOJO]

  def getProofsForModel(modelId: String): List[ProofPOJO] = getProofsForModel(modelId.toInt)

  def deleteProof(proofId: Int) : Boolean

  //Proofs and Proof Nodes
  def getProofInfo(proofId: Int): ProofPOJO

  def getProofInfo(proofId: String): ProofPOJO = getProofInfo(proofId.toInt)

  def updateProofInfo(proof: ProofPOJO)

  def updateProofName(proofId: Int, name: String): Unit = {
    val info = getProofInfo(proofId)
    updateProofInfo(new ProofPOJO(proofId, info.modelId, name, info.description, info.date, info.stepCount, info.closed))
  }

  def updateProofName(proofId: String, name: String): Unit = updateProofName(proofId.toInt, name)

  def addAgendaItem(proofId: Int, initialProofNode: Int, displayName:String): Int

  def getAgendaItem(proofId: Int, initialProofNode: Int): Option[AgendaItemPOJO]

  def updateAgendaItem(item:AgendaItemPOJO): Unit

  def agendaItemsForProof(proofId: Int): List[AgendaItemPOJO]

  // Tactics
  /** Stores a Provable in the database and returns its ID */
  def createProvable(p: Provable): Int

  /** Reconstruct a stored Provable */
  def getProvable(provableId: Int): ProvablePOJO

  /** Deletes a provable and all associated sequents / formulas */
  def deleteProvable(provableId: Int): Boolean

  /////////////////////

  /** Creates a new execution and returns the new ID in tacticExecutions */
  def createExecution(proofId: Int): Int

  /** Deletes an execution from the database */
  def deleteExecution(executionId: Int): Boolean

  /**
    * Adds an execution step to an existing execution
    *
    * @note Implementations should enforce additional invarants -- never insert when branches or alt orderings overlap.
    */
  def addExecutionStep(step: ExecutionStepPOJO): Int

  /** Truncate the execution trace at the beginning of alternativeTo and replace it with trace. */
  def addAlternative(alternativeTo: Int, inputProvable: Provable, trace:ExecutionTrace)

  /** Return the sequence of steps that led to the current state of the proof. */
  def getExecutionTrace(proofID: Int): ExecutionTrace

  /** Return a list of all finished execution steps in the current history of the execution, in the order in which they
    * occurred.
    * @note For most purposes, getExecutionTrace is more convenient, but slower. */
  def getExecutionSteps(executionId: Int) : List[ExecutionStepPOJO]

  /** Update existing execution step. */
  def updateExecutionStep(executionStepId: Int, step:ExecutionStepPOJO): Unit

  /////////////////////
  /** Adds a bellerophon expression as an executable and returns the new executableId */
  def addBelleExpr(expr: BelleExpr): Int

  /** Returns the executable with ID executableId */
  def getExecutable(executableId: Int): ExecutablePOJO
}
