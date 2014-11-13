package edu.cmu.cs.ls.keymaera.hydra

import com.mongodb.casbah.Imports._

/**
 * Created by nfulton on 9/23/14.
 */
object MongoDB extends DBAbstraction {
  val mongoClient = MongoClient("localhost", 27017)

  //Collections.
  val users   = mongoClient("keymaera")("users")
  val models  = mongoClient("keymaera")("models")
  val proofs  = mongoClient("keymaera")("proofs")
  val logs    = mongoClient("keymaera")("logs")
  val tasks   = mongoClient("keymaera")("tasks")
  val tactics = mongoClient("keymaera")("tactics")
  val dispatchedTactics = mongoClient("keymaera")("dispatchedTactics")
  val sequents = mongoClient("keymaera")("sequents")

  def cleanup() = {
    users.drop()
    models.drop()
    proofs.drop()
    logs.drop()
    tasks.drop()
  }

  //val proofs = mongoClient("keymaera")("proofs")
  //val tactics = mongoClient("keymaera")("tactics")
  //val positionTactics = mongoClient("keymaera")("positionTactics")
  //val models = mongoClient("keymaera")("models")

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Users
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
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
  override def createModel(userId: String, name: String, fileContents: String, currentDate : String): Boolean = {

    var query = MongoDBObject("userId" -> userId, "name" -> name, "fileContents" -> fileContents) //w/o date
    if(models.find(query).length == 0) {
      var obj = MongoDBObject("userId" -> userId, "name" -> name, "date" -> currentDate, "fileContents" -> fileContents)
      models.insert(obj)
      true // TODO should we allow models by the same user and with the same name?
    }
    else {
      false
    }
  }

  override def getModelList(userId : String) = {
    var query = MongoDBObject("userId" -> userId)
    val allModels = models.find(query)
    allModels.map(model =>
      if(!model.containsField("_id")) ???
      else new ModelPOJO(
        model.getAs[ObjectId]("_id").getOrElse(null).toString(),
        model.getAs[String]("userId").getOrElse(""),
        model.getAs[String]("name").getOrElse("") ,
        model.getAs[String]("date").getOrElse(""),
        model.getAs[String]("fileContents").getOrElse("")
      )
    ).toList
  }

  override def getModel(modelId: String): ModelPOJO = {
    var query = MongoDBObject("_id" -> new ObjectId(modelId))
    val results = models.find(query)
    if(results.length > 1) ??? //There should only be one response b/c _id is a pk.
    if(results.length < 1) throw new Exception(modelId + " is a bad modelId!")
    results.map(result => new ModelPOJO(
      result.getAs[ObjectId]("_id").getOrElse(null).toString(),
      result.getAs[String]("userId").getOrElse(""),
      result.getAs[String]("name").getOrElse("") ,
      result.getAs[String]("date").getOrElse(""),
      result.getAs[String]("fileContents").getOrElse("")
    )).toList.last
  }

  override def createProofForModel(modelId : String, name : String, description : String, date:String) : String = {
    var query = MongoDBObject("modelId" -> modelId, "name" -> name, "description" -> description, "date" -> date,
      "steps" -> List[String]())
    var result = proofs.insert(query)
    query.get("_id").toString()
  }

  override def getProofsForModel(modelId : String) : List[ProofPOJO] = {
    var query = MongoDBObject("modelId" -> modelId)
    var results = proofs.find(query)
    if(results.length < 1) Nil
    else {
      results.map(result => {
        //TODO count the number of steps
        val stepCount = -1
        //TODO determine if the proof is closed
        val isClosed = false

        new ProofPOJO(
          result.getAs[ObjectId]("_id").getOrElse(null).toString(),
          result.getAs[String]("modelId").getOrElse(null).toString(),
          result.getAs[String]("name").getOrElse(null).toString(),
          result.getAs[String]("description").getOrElse("no description"),
          result.getAs[String]("date").getOrElse(null).toString(),
          stepCount,
          isClosed
        )
      }).toList
    }
  }

  override def getProofInfo(proofId: String): ProofPOJO = {
    var query = MongoDBObject("_id" -> new ObjectId(proofId))
    val results = proofs.find(query)
    if(results.length > 1) throw new IllegalStateException("Proof ID " + proofId + " is not unique") //There should only be one response b/c _id is a pk.
    if(results.length < 1) throw new IllegalArgumentException(proofId + " is a bad proofId!")
    results.map(result => new ProofPOJO(
      result.getAs[ObjectId]("_id").getOrElse(null).toString(),
      result.getAs[String]("modelId").getOrElse(""),
      result.getAs[String]("name").getOrElse(""),
      result.getAs[String]("description").getOrElse("") ,
      result.getAs[String]("date").getOrElse(""),
      result.getAs[Integer]("stepCount").getOrElse(0),
      result.getAs[Boolean]("closed").getOrElse(false)
    )).toList.last
  }

  override def getProofSteps(proofId: String) : List[String] = {
    val query = MongoDBObject("_id" -> new ObjectId(proofId))
    val results = proofs.find(query)
    if(results.length > 1) throw new IllegalStateException("Proof ID " + proofId + " is not unique")
    if(results.length < 1) throw new IllegalArgumentException(proofId + " is a bad proofId!")
    results.one().getAs[List[String]]("steps").getOrElse(List[String]())
  }

  override def addFinishedTactic(proofId: String, tacticInstId: String) = {
    val query = MongoDBObject("_id" -> new ObjectId(proofId))
    val results = proofs.find(query)
    if(results.length > 1) throw new IllegalStateException("Proof ID " + proofId + " is not unique")
    if(results.length < 1) throw new IllegalArgumentException(proofId + " is a bad proofId!")
    val steps = results.one().getAs[List[String]]("steps").getOrElse(List[String]()) :+ tacticInstId
    val update = $set("steps" -> steps)
    proofs.update(MongoDBObject("_id" -> new ObjectId(proofId)), update)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Tactics
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  def createTactic(name : String, clazz : String, kind : TacticKind.Value) : String = {
    val query = MongoDBObject(
      "name"    -> name,
      "clazz"   -> clazz,
      "kind"    -> kind.toString()
    )
    tactics.insert(query)
    query.get("_id").toString()
  }
  def getTactic(id: String) : TacticPOJO = {
    val query = MongoDBObject("_id" -> new ObjectId(id))
    val results = tactics.find(query)
    if(results.length < 1 || results.length > 1) ??? //TODO handle db errors
    results.map(result => new TacticPOJO(
      result.getAs[ObjectId]("_id").orNull.toString(),
      result.getAs[String]("name").getOrElse(""),
      result.getAs[String]("clazz").getOrElse(""),
      TacticKind.withName(result.getAs[String]("kind").getOrElse(""))
    )).toList.last
  }
  def getTacticByName(name: String) : Option[TacticPOJO] = {
    val query = MongoDBObject("name" -> name)
    val results = tactics.find(query)
    if(results.length > 1) ??? //TODO handle db errors
    if (results.length < 1) None
    else Some(results.map(result => new TacticPOJO(
      result.getAs[ObjectId]("_id").orNull.toString(),
      result.getAs[String]("name").getOrElse(""),
      result.getAs[String]("clazz").getOrElse(""),
      TacticKind.withName(result.getAs[String]("kind").getOrElse(""))
    )).toList.last)
  }
  override def getTactics() : List[TacticPOJO] = {
    val results = tactics.find()
    results.map(result => new TacticPOJO(
      result.getAs[ObjectId]("_id").orNull.toString(),
      result.getAs[String]("name").getOrElse(""),
      result.getAs[String]("clazz").getOrElse(""),
      TacticKind.withName(result.getAs[String]("kind").getOrElse(""))
    )).toList
  }

  override def createDispatchedTactics(proofId:String, nodeId:Option[String], formulaId:Option[String], tacticsId:String,
                                        status:DispatchedTacticStatus.Value) : String = {
    val fields = List(
      "proofId"       -> proofId,
      "tacticsId"    -> tacticsId,
      "status"       -> status.toString)
    if (nodeId.isDefined) { fields :+ ("nodeId" -> nodeId) }
    if (formulaId.isDefined) { fields :+ ("formulaId" -> formulaId) }

    val query = MongoDBObject(fields)
    dispatchedTactics.insert(query)
    query.get("_id").toString()
  }
  override def getDispatchedTactics(tId : String) : DispatchedTacticPOJO = {
    val query = MongoDBObject("_id" -> new ObjectId(tId))
    val results = dispatchedTactics.find(query)
    if(results.length < 1 || results.length > 1) ??? //TODO handle db errors
    results.map(result => new DispatchedTacticPOJO(
      result.getAs[ObjectId]("_id").orNull.toString(),
      result.getAs[String]("proofId").getOrElse(""),
      if (result.containsField("nodeId")) Some(result.getAs[String]("nodeId").getOrElse("")) else None,
      if (result.containsField("formulaId")) Some(result.getAs[String]("formulaId").getOrElse("")) else None,
      result.getAs[String]("tacticsId").getOrElse(""),
      DispatchedTacticStatus.withName(result.getAs[String]("status").getOrElse(""))
    )).toList.last
  }
  override def updateDispatchedTactics(tactic : DispatchedTacticPOJO) = {
    val fields = List(
      "proofId"       -> tactic.proofId,
      "tacticsId"    -> tactic.tacticsId,
      "status"       -> tactic.status.toString)
    if (tactic.nodeId.isDefined) { fields :+ ("nodeId" -> tactic.nodeId) }
    if (tactic.formulaId.isDefined) { fields :+ ("formulaId" -> tactic.formulaId) }

    val update = MongoDBObject(fields)
    dispatchedTactics.update(MongoDBObject("_id" -> new ObjectId(tactic.id)), update)
  }

}
