package edu.cmu.cs.ls.keymaera.hydra

import java.io.{InputStreamReader, BufferedReader}
import java.util

import edu.cmu.cs.ls.keymaera.api.KeYmaeraInterface.PositionTacticAutomation
import edu.cmu.cs.ls.keymaera.api.KeYmaeraInterface.PositionTacticAutomation.PositionTacticAutomation

import scala.io.Source

//Global setting:
object DBAbstractionObj {
  def defaultDatabase = SQLite
}

// POJOs, short for Plain Old Java Objects, are for us just tagged products.
object TacticKind extends Enumeration {
  type TacticKind = Value
  val Tactic, PositionTactic, InputTactic, InputPositionTactic, UserTactic = Value
}

object DispatchedTacticStatus extends Enumeration {
  type DispatchedTacticStatus = Value
  val Prepared, Running, Finished, Aborted = Value

  def fromString(s : String) = s match {
    case "Prepared" => Prepared
    case "Running" => Running
    case "Finished" => Finished
    case "Aborted" => Aborted
    case _ => throw new Exception("Status " + s + " not in enum.")
  }
}

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

/**
 * Data object for tactics.
 * @param tacticId Identifies the tactic.
 * @param name The name of the tactic.
 * @param clazz The tactic implementation.
 * @param kind The kind of tactic.
 */
class TacticPOJO(val tacticId:String, val name:String, val clazz:String, val kind : TacticKind.Value)


abstract class AbstractDispatchedPOJO

/**
 * Data object for a tactic instance running on the specified formula of a particular proof (node).
 * @param id Identifies the tactic instance.
 * @param proofId Identifies the proof.
 * @param nodeId Identifies the node. If None, it identifies the "root" node of task nodes.
 * @param formulaId Identifies the formula.
 * @param tacticsId Identifies the tactic that is being run.
 */
case class DispatchedTacticPOJO(val id:String, val proofId:String, val nodeId:Option[String], val formulaId:Option[String],
                           val tacticsId:String, val input:Map[Int,String],
                           val auto:Option[PositionTacticAutomation.Value], val status:DispatchedTacticStatus.Value) extends AbstractDispatchedPOJO

case class DispatchedCLTermPOJO(val id : String, val proofId : String, val nodeId : Option[String], val clTerm : String, val status:Option[DispatchedTacticStatus.Value]) extends AbstractDispatchedPOJO

class ConfigurationPOJO(val name: String, val config: Map[String,String])

//tasks : _id, model
//tactics: _id, name, class
//dispatched_tactics: _id, tactic_id, task_id, node_id, count


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
  def getProofSteps(proofId : String) : List[String]

  // Tactics
  def createTactic(name : String, clazz : String, kind : TacticKind.Value) : String
  def tacticExists(id: String) : Boolean
  def getTactic(id: String) : Option[TacticPOJO]
  def getTacticByName(name: String) : Option[TacticPOJO]
  def getTactics : List[TacticPOJO]
  def createDispatchedTactics(taskId:String, nodeId:Option[String], formulaId:Option[String], tacticsId:String,
                              input:Map[Int, String], auto: Option[PositionTacticAutomation.PositionTacticAutomation],
                              status:DispatchedTacticStatus.Value) : String
  def updateDispatchedTactics(tactic:DispatchedTacticPOJO)
  def getDispatchedTactics(tId : String) : Option[DispatchedTacticPOJO]
  def getDispatchedTermOrTactic(tId : String) : Option[AbstractDispatchedPOJO]
  def updateProofOnTacticCompletion(proofId: String, tId: String)

  def createDispatchedCLTerm(taskId : String, nodeId : Option[String], clTerm : String) : String
  def getDispatchedCLTerm(id : String) : Option[DispatchedCLTermPOJO]
  def updateDispatchedCLTerm(termToUpdate : DispatchedCLTermPOJO)
  def updateProofOnCLTermCompletion(proofId : String, termId : String)

  import spray.json._ //allows for .parseJoson on strings.
  protected def initializeForDemo() : Unit = {
    println("Initializing a demo database")

    //Add user
    this.createUser("guest", "guest")

    val reader = this.getClass.getResourceAsStream("/examples/index.txt")
    val contents: String = Source.fromInputStream(reader).getLines().foldLeft("")((file, line) => file + "\n" + line)
    val source: JsArray = contents.parseJson.asInstanceOf[JsArray]
    source.elements.map(processJsonForSingleModel(_, false))
  }

  def getFileContents(file : String) = {
    val reader = this.getClass.getResourceAsStream(file)
    if(reader == null) throw new Exception("Could not find problem file.")
    Source.fromInputStream(reader).getLines().foldLeft("")((file, line) => file + "\n" + line)
  }

  def processJsonForSingleModel(element : JsValue, runTactic : Boolean) = {
    val kvps = element.asJsObject.fields.map(kvp =>
      (kvp._1, kvp._2.asInstanceOf[JsString].value.toString)
    )
    val name = kvps.get("name").getOrElse(throw new Exception("Expcted a name but found none."))
    val file = kvps.get("file").getOrElse(throw new Exception("Expcted a file but found none."))
    val fileContents = getFileContents("/" + file)
    val description = kvps.get("description")
    val publink = kvps.get("publicnk")
    val title = kvps.get("title")
    val tactic = kvps.get("tactic")

    val id = this.createModel("guest", name, fileContents, new java.util.Date().toString(), description, publink, title, tactic) match {
      case Some(x) => x
      case None => throw new Exception("Could not retrieve ID generated by insert.")
    }

    val tacticContents = tactic match {
      case Some(tacticFile) => Some(getFileContents("/" + tacticFile))
      case None => None
    }

    //Run the tactic (optionally)
    if (tacticContents.isDefined && runTactic)
      new RunCLTermRequest(this, "guest", id, None, tacticContents.get).getResultingResponses();
  }
}