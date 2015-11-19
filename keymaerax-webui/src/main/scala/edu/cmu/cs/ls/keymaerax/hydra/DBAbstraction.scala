/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.hydra

import java.nio.channels.Channels

import edu.cmu.cs.ls.keymaerax.api.KeYmaeraInterface.PositionTacticAutomation

import java.io.File
import java.io.FileOutputStream

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.core.{Sequent, Provable}
import edu.cmu.cs.ls.keymaerax.hydra.ExecutionStepStatus.ExecutionStepStatus
import edu.cmu.cs.ls.keymaerax.hydra.ParameterValueType.ParameterValueType

import scala.io.Source
import spray.json.DefaultJsonProtocol._

//Global setting:
object DBAbstractionObj {
  def defaultDatabase = SQLite //this needs to be a def and not a val because DBAbstractionObj is initialized in SQLite.
  val dblocation: String = {
    new File(
      System.getProperty("user.home") + File.separator +
        ".keymaerax"
    ).mkdirs()

    val file = new File(System.getProperty("user.home") + File.separator +
      ".keymaerax" + File.separator + "keymaerax.sqlite")
    file.getCanonicalPath
  }
  println(dblocation)
}

class ConfigurationPOJO(val name: String, val config: Map[String,String])

/**
 * Data object for models.
 * @param modelId Identifies the model.
 * @param userId Identifies the user.
 * @param name The name of the model.
 * @param date The creation date.
 * @param keyFile The model file content.
 * @param description The description of the model.
 * @param pubLink Link to additional information (paper) on the model.
 */
class ModelPOJO(val modelId:String, val userId:String, val name:String, val date:String, val keyFile:String,
                val description:String, val pubLink:String, val title:String, val tactic : Option[String]) //the other guys on this linke should also be optional.

/**
 * Data object for proofs. A proof
 * @param proofId Identifies the proof.
 * @param modelId Identifies the model.
 * @param name The proof name.
 * @param description A proof description.
 * @param date The creation date.
 * @param stepCount The number of proof steps in the proof.
 * @param closed Indicates whether the proof is closed (finished proof) or not (partial proof).
 */
class ProofPOJO(val proofId:String, val modelId:String, val name:String, val description:String,
                val date:String, val stepCount : Integer, val closed : Boolean)

case class ProvablePOJO(provableId: String, conclusionId: String)

case class SequentPOJO(sequentId: String, provableId: String)

case class SequentFormulaPOJO(sequentFormulaId: String, sequentId: String, isAnte: Boolean, index: Int, formulaStr: String)

object ExecutionStepStatus extends Enumeration {
  type ExecutionStepStatus = Value
  val Prepared, Running, Finished, Aborted, Error, DependsOnChildren = Value

  def fromString(s : String) = s match {
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
    case DependsOnChildren => "DependsOnChilden"
  }
}

case class TacticExecutionPOJO(executionId: String, proofId: String)

case class ExecutionStepPOJO(stepId: String, executionId: String,
                             previousStep: String, parentStep: String,
                             branchOrder: Option[String],
                             branchLabel: Option[Int],
                             alternativeOrder: Int,
                             status: ExecutionStepStatus,
                             executableId: String,
                             inputProvableId: String,
                             resultProvableId: String,
                             userExecuted: Boolean)
{
  require(branchOrder.isEmpty != branchLabel.isEmpty) //also schema constraint
}

case class ExecutablePOJO(executableId: String, scalaTacticId: Option[String], belleExpr: Option[String]) {
  require(scalaTacticId.isEmpty != belleExpr.isEmpty)
}

/*
CREATE TABLE IF NOT EXISTS `scalaTactics` (
  `scalaTacticId` TEXT PRIMARY KEY ON CONFLICT FAIL,
  `location`      TEXT
);
*/
case class ScalaTacticPOJO(scalaTacticId: String, location: String)


case class ParameterPOJO(parameterId: String, executableID: String, idx: Int, valueType: ParameterValueType, value: String)


object ParameterValueType extends Enumeration {
  type ParameterValueType = Value
  val String, Position, Formula, Provable = Value

  def fromString(s : String) = s match {
    case "0" => String
    case "1" => Position
    case "2" => Formula
    case "3" => Provable
    case _ => throw new Exception("ParameterValueType " + s + " not in enum.")
  }
}

case class USubstPatternParameterPOJO(patternId: String, executableId: String,
                                  index: Int, patternFormulaStr: String, resultingExecutableId: String)

/**
 * Proof database
 */
trait DBAbstraction {
  /**
   * Initializes a new database.
   */
  def cleanup() : Unit

  // Configuration
  def getAllConfigurations: Set[ConfigurationPOJO]
  def getConfiguration(configName: String) : ConfigurationPOJO
  def createConfiguration(configName: String) : Boolean
  def updateConfiguration(config: ConfigurationPOJO)

  // Users
  def userExists(username : String) : Boolean
  def createUser(username : String, password : String) : Unit
  def getUsername(uid : String) : String
  def checkPassword(username : String, password : String) : Boolean
  def getProofsForUser(userId : String) : List[(ProofPOJO, String)] //the string is a model name.
  def openProofs(userId : String) : List[ProofPOJO]

  //Models
  def createModel(userId: String, name : String, fileContents : String, date:String,
                  description : Option[String]=None, publink:Option[String]=None,
                  title:Option[String]=None, tactic:Option[String]=None) : Option[String]
  def getModel(modelId : String) : ModelPOJO
  def getModelList(userId : String) : List[ModelPOJO] // name, date, fileContents
  //Proofs of models
  def createProofForModel(modelId : String, name : String, description : String, date : String) : String //returns id of create object
  def getProofsForModel(modelId : String) : List[ProofPOJO]

  //Proofs and Proof Nodes
  def getProofInfo(proofId : String) : ProofPOJO
  def updateProofInfo(proof: ProofPOJO)
  def updateProofName(proofId : String, name : String)
  def getProofSteps(proofId : String) : List[String]

  // Tactics
  /** Stores a Provable in the database and returns its ID */
  def serializeProvable(p : Provable): String

  /** Gets the conclusion of a provable */
  def getConclusion(provableId: String): Sequent

  /** Use escape hatch in prover core to create a new Provable */
  def loadProvable(provableId: String): Sequent

  /** Deletes a provable and all associated sequents / formulas */
  def deleteProvable(provableId: String): Unit

  /////////////////////

  /** Creates a new execution and returns the new ID in tacticExecutions */
  def createExecution(proofId: String): String

  /** Deletes an execution from the database */
  def deleteExecution(executionId: String): Unit

  /**
    * Adds an execution step to an existing execution
    * @note Implementations should enforce additional invarants -- never insert when branches or alt orderings overlap.
    */
  def addExecutionStep(step: ExecutionStepPOJO): String

  def getExecutionSteps(executionID: String) : List[ExecutionStepPOJO]

  /** Updates an executable step's status. @note should not be transitive */
  def updateExecutionStatus(executionStepId: String, status: ExecutionStepStatus): Unit

  /////////////////////

  /** Adds a new scala tactic and returns the resulting id */
  def addScalaTactic(scalaTactic: ScalaTacticPOJO): String

  /** Adds a bellerophon expression as an executable and returns the new executableId */
  def addBelleExpr(expr: BelleExpr, params: List[ParameterPOJO]): String

  /** Adds a built-in tactic application using a set of parameters */
  def addAppliedScalaTactic(scalaTacticId: String, params: List[ParameterPOJO]): String

  /** Returns the executable with ID executableId */
  def getExecutable(executableId: String): ExecutablePOJO

  import spray.json._ //allows for .parseJoson on strings.
  def initializeForDemo2() : Unit = {
    println("Initializing a demo database")

    //Add user
    this.createUser("guest", "guest")

    val reader = this.getClass.getResourceAsStream("/examples/index.txt")
    val contents: String = Source.fromInputStream(reader).getLines().foldLeft("")((file, line) => file + "\n" + line)
    val source: JsArray = contents.parseJson.asInstanceOf[JsArray]
    source.elements.map(processJsonForSingleModel(_))
  }

  private def getFileContents(file : String) = {
    val reader = this.getClass.getResourceAsStream(file)
    if(reader == null) throw new Exception(s"Could not find problem file $file.")
    Source.fromInputStream(reader).getLines().foldLeft("")((file, line) => file + "\n" + line)
  }

  private def processJsonForSingleModel(element : JsValue) = {
    val kvps = element.asJsObject.fields.map(kvp =>
      (kvp._1, kvp._2.convertTo[String])
    )
    val name = kvps.getOrElse("name", throw new Exception("Expcted a name but found none."))
    val file = kvps.getOrElse("file", throw new Exception("Expcted a file but found none."))
    val fileContents = getFileContents("/" + file)
    val description = kvps.get("description")
    val publink = kvps.get("pubLink")
    val title = kvps.get("title")
    val tacticContent = kvps.get("tactic") match {
      case Some(tf) => Some(getFileContents("/" + tf))
      case None => None
    }

    val id = createModel("guest", name, fileContents, new java.util.Date().toString, description, publink, title,
                         tacticContent) match {
      case Some(x) => x
      case None => throw new Exception("Could not retrieve ID generated by insert.")
    }
  }
}
