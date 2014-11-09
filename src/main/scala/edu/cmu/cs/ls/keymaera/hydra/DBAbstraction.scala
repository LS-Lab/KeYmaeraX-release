package edu.cmu.cs.ls.keymaera.hydra

import edu.cmu.cs.ls.keymaera.core.{Sequent, ProofNode}


// POJOs, short for Plain Old Java Objects, are for us just tagged products.

class ModelPOJO(val modelId:String, val userId:String, val name:String, val date:String, val keyFile:String)
class ProofPOJO(val modelId:String, val proofId:String, val name:String, val description:String, val date:String, val stepCount : Integer, val closed : Boolean)
class TaskPOJO(val taskId:String, val task:String, val rootTaskId:String, val proofId:String)
class TacticsPOJO(val tacticsId:String)
class DispatchedTacticsPOJO(val id:String, val taskId:String, val nodeId:String, val formulaId:String, val tacticsId:String)

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
  def createDispatchedTactics(taskId:String, nodeId:String, formulaId:String, tacticsId:String) : String
  def getDispatchedTactics(tId : String) : DispatchedTacticsPOJO
}