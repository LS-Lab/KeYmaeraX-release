package edu.cmu.cs.ls.keymaera.hydra

import edu.cmu.cs.ls.keymaera.core.{Sequent, ProofNode}


// POJOs, short for Plain Old Java Objects, are for us just tagged products.
object TacticKind extends Enumeration {
  type TacticKind = Value
  val Tactic, PositionTactic, InputTactic, InputPositionTactic, UserTactic = Value
}

object DispatchedTacticStatus extends Enumeration {
  type DispatchedTacticStatus = Value
  val Prepared, Running, Finished, Aborted = Value
}

/**
 * Data object for models.
 * @param modelId Identifies the model.
 * @param userId Identifies the user.
 * @param name The name of the model.
 * @param date The creation date.
 * @param keyFile The model file content.
 */
class ModelPOJO(val modelId:String, val userId:String, val name:String, val date:String, val keyFile:String)

/**
 * Data object for proofs. A proof
 * @param modelId Identifies the model.
 * @param proofId Identifies the proof.
 * @param name The proof name.
 * @param description A proof description.
 * @param date The creation date.
 * @param stepCount The number of proof steps in the proof.
 * @param closed Indicates whether the proof is closed (finished proof) or not (partial proof).
 */
class ProofPOJO(val modelId:String, val proofId:String, val name:String, val description:String,
                val date:String, val stepCount : Integer, val closed : Boolean)

/**
 * Data object for tasks.
 * @param taskId Identifies the task.
 * @param nodeId Identifies the node. If None, it identifies the "root" node of task nodes.
 * @param task The task description (a sequent in JSON format as created by the backend).
 * @param rootTaskId Back link to the "root" node of task nodes.
 * @param proofId Identifies the proof.
 */
class TaskPOJO(val taskId:String, val nodeId:Option[String], val task:String, val rootTaskId:String, val proofId:String)

/**
 * Data object for tactics.
 * @param tacticId Identifies the tactic.
 * @param name The name of the tactic.
 * @param clazz The tactic implementation.
 * @param kind The kind of tactic.
 */
class TacticPOJO(val tacticId:String, val name:String, val clazz:String, val kind : TacticKind.Value)

/**
 * Data object for a tactic instance running on the specified formula of a particular task (node).
 * @param id Identifies the tactic instance.
 * @param taskId Identifies the task.
 * @param nodeId Identifies the node. If None, it identifies the "root" node of task nodes.
 * @param formulaId Identifies the formula.
 * @param tacticsId Identifies the tactic that is being run.
 */
class DispatchedTacticPOJO(val id:String, val taskId:String, val nodeId:Option[String], val formulaId:Option[String],
                           val tacticsId:String, val status:DispatchedTacticStatus.Value)

/**
 * Proof database
 */
trait DBAbstraction {
  /**
   * Initializes a new database.
   */
  def cleanup() : Unit

  // Users
  def userExists(username : String) : Boolean
  def createUser(username : String, password : String) : Unit
  def getUsername(uid : String) : String
  def checkPassword(username : String, password : String) : Boolean

  //Models
  def createModel(userId: String, name : String, fileContents : String, date:String) : Boolean
  def getModel(modelId : String) : ModelPOJO
  def getModelList(userId : String) : List[ModelPOJO] // name, date, fileContents
  //Proofs of models
  def createProofForModel(modelId : String, name : String, description : String, date : String) : String //returns id of create object
  def getProofsForModel(modelId : String) : List[ProofPOJO]

  //Proofs and Proof Nodes
  def getProofInfo(proofId : String) : ProofPOJO

  // Proof trees
  def subtreeExists(pnId : String) : Boolean
  def createSubtree(pnId : String, tree : String) : String
  def getSubtree(pnId : String) : String
  def updateSubtree(pnId: String, tree : String)

  // Tasks
  def createTask(proofId: String) : String
  def addTask(task : TaskPOJO)
  def getTask(taskId : String) : TaskPOJO
  def getProofTasks(proofId : String) : List[TaskPOJO]
  def updateTask(task: TaskPOJO)

  // Tactics
  def createTactic(name : String, clazz : String, kind : TacticKind.Value) : String
  def getTactic(id: String) : TacticPOJO
  def getTacticByName(name: String) : Option[TacticPOJO]
  def getTactics() : List[TacticPOJO]
  def createDispatchedTactics(taskId:String, nodeId:Option[String], formulaId:Option[String], tacticsId:String,
                              status:DispatchedTacticStatus.Value) : String
  def updateDispatchedTactics(tactic:DispatchedTacticPOJO)
  def getDispatchedTactics(tId : String) : DispatchedTacticPOJO
}