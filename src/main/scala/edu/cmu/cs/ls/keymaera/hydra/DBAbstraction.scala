package edu.cmu.cs.ls.keymaera.hydra

/**
 * Proof database
 */
trait DBAbstraction {
  // Users
  def userExists(username : String) : Boolean
  def createUser(username : String, password : String) : Unit
  def getUsername(uid : String) : String
  def checkPassword(username : String, password : String) : Boolean

  // Models
  def createModel(userId: String, name : String, fileContents : String) : Boolean
  def getModel(modelId : String) : (String, String)
  def getModelList(userId : String) : List[(String, String)] // or so?

  //Proofs and Proof Nodes
  /**
   * This method is called when a tactic completes. It should store the result of the method in the DB.
   */
  def tacticCompletionHook : Any => Any

  def getSubtree(pnId : Int) : String
}