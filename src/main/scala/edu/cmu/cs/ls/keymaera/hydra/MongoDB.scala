package edu.cmu.cs.ls.keymaera.hydra

import com.mongodb.casbah.Imports._

/**
 * Created by nfulton on 9/23/14.
 */
object MongoDB extends DBAbstraction {
  val mongoClient = MongoClient("localhost", 27017)

  //val proofs = mongoClient("keymaera")("proofs")
  //val tactics = mongoClient("keymaera")("tactics")
  //val positionTactics = mongoClient("keymaera")("positionTactics")
  //val models = mongoClient("keymaera")("models")

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Users
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  val users = mongoClient("keymaera")("users")
  users.drop() // TODO-nrf remove.

  override def getUsername(uid: String): String = uid

  override def userExists(username : String) = {
    val query = MongoDBObject("username" -> username)
    users.count(query) > 0
  }

  override def createUser(username: String, password: String): Unit = {
    val newUser = MongoDBObject("username" -> username, "password" -> password)
    users.insert(newUser)
  }

  override def checkPassword(username: String, password: String): Boolean = {
    val result = MongoDBObject("username" -> username, "password" -> password)
    users.count(result) > 0
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Models
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  val models = mongoClient("keymaera")("models")

  override def createModel(userId: String, name: String, fileContents: String): Boolean = {
    var obj = MongoDBObject("userId" -> userId, "name" -> name, "fileContents" -> fileContents)
    models.insert(obj)
    return true // should we allow models by the same user and with the same name?
  }

  override def getModelList(userId : String) = ???

  override def getModel(modelId: String): (String, String) = ???

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Proof Nodes
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  override def getSubtree(pnId: Int): String = ???

  /**
   * This method is called when a tactic completes. It should store the result of the method in the DB.
   */
  override def tacticCompletionHook: (Any) => Any = ???

}
