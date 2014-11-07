//package edu.cmu.cs.ls.keymaera.hydra
//import com.mongodb.casbah.Imports._
//import edu.cmu.cs.ls.keymaera.api.KeYmaeraInterface
//import edu.cmu.cs.ls.keymaera.core.{ProofStepInfo, ProofNodeInfo}
//import org.bson.BSONObject
//import com.mongodb.util.JSON
//import org.bson.types.ObjectId
//import edu.cmu.cs.ls.keymaera.tactics.Tactics
//
///**
//* Created by jdq on 6/12/14.
//*/
//object ProverBusinessLogic {
//
//  val mongoClient = MongoClient("localhost", 27017)
//  val proofs = mongoClient("keymaera")("proofs")
//  val tactics = mongoClient("keymaera")("tactics")
//  val positionTactics = mongoClient("keymaera")("positionTactics")
//  val models = mongoClient("keymaera")("models")
//
//
//
//  // FIXME: in the long run this should only make sure that the database state is consistent
//  proofs.dropCollection
//  tactics.dropCollection
//  positionTactics.dropCollection
//  models.dropCollection
//
//  initTactics
//
//  //FIXME in the long run we need to save everything in the database to restart KeYmaera
//  def initTactics =
//    for((i, s) <- KeYmaeraInterface.getTactics)
//      tactics.insert(MongoDBObject("tacticId" -> i, "name" -> s))
//    for((i, s) <- KeYmaeraInterface.getPositionTactics)
//      tactics.insert(MongoDBObject("tacticId" -> i, "name" -> s))
//
//  def getTactic(i: Int): String = tactics.find(MongoDBObject("tacticId" -> i)).one.get("_id").toString
//
//  /**
//   * Add a new model to the database. This will return a unique identifier for this model.
//   * Each model will have a parser status in the database
//   *
//   * @param content the content to be added to the database which will be parsed by KeYmaera
//   * @return a unique identifier for the model
//   */
//  def addModel(content: String): String = {
//      val (tId, model) = KeYmaeraInterface.addTask(content)
//      println("Parsed " + model)
//      val jsonModel = JSON.parse(model)
//      val query = MongoDBObject("taskId" -> tId, "nodeId" -> tId)
//      models += query
//      val ins = models.find(query).one
//      println("Result is " + ins)
//      val id = ins("_id").asInstanceOf[ObjectId]
//      val q2 = ("model" -> store(jsonModel.asInstanceOf[DBObject], id)("_id"))
//      models.update(MongoDBObject("_id" -> id), $set(q2))
//      id.toString
//  }
//
//  /**
//   * This API call is used to dispatch a tactic. It will return true if the tactic has been dispatched successfully
//   * and false otherwise. Once the tactic has been completed all its results will become visible in the database.
//   *
//   * @param tacticId
//   * @param pnId
//   * @return the tactic instance ID
//   */
//  def runTactic(tacticId: String, pnId: String, nId: String, formulaId: Option[String], callback: String => Unit = _ => ()): Option[Int] = {
//    println("Run tactic called")
//    val tactic = tactics.find(MongoDBObject("_id" -> new ObjectId(tacticId)))
//    println("Tactic is " + tactic)
//    val proof = models.find(MongoDBObject("_id" -> new ObjectId(pnId))).one
//    val node = proofs.find(MongoDBObject("_id" -> new ObjectId(nId))).one
//    // TODO create a new tactics instance in the DB, hand ID to KeYmaera
//    println("Node is " + node)
//    require(tactic.length == 1, "tactic.length = " + tactic.length + " should be 1")
//    val t = tactic.one
//    (proof.get("taskId"), node.get("sequent").asInstanceOf[DBObject].get("nodeId"), t.get("tacticId")) match {
//      case (tId: Integer, nodeId: String, tacId: Integer) =>
//        println("Actually running tactic on node " + nodeId)
//        val tacticInstId = if(proof("_id") == node("_id"))
//          KeYmaeraInterface.runTactic(tId, None, tacId, formulaId, Some(tacticCompleted(callback, node)))
//        else
//          KeYmaeraInterface.runTactic(tId, Some(nodeId), tacId, formulaId, Some(tacticCompleted(callback, node)))
//        // TODO store tactics instance in DB
//        tacticInstId
//      case _ => None
//    }
//  }
//
//private def store(q: DBObject, id: ObjectId = new ObjectId): MongoDBObject = {
//    val res = new MongoDBObject
//    res.put("_id", id)
//    for(key <- q.keys) {
//      if(key == "children") {
//        res.put(key, store(q.getAs[MongoDBList]("children").get))
//      } else {
//        res.put(key, q(key))
//      }
//    }
//    println("Inner obj: " + res)
//    proofs.insert(res)
//    res
//  }
//
//  private def store(cs: MongoDBList): Seq[String] = {
//    for(c <- cs) yield store(c.asInstanceOf[DBObject])("_id").toString
//  }
//
//  private def tacticCompleted(f: String => Unit, pn: BSONObject)(i: Int)(taskId: Int, nId: Option[String], tacticId: Int) {
//    println("Tactic completed " + tacticId + "(instance ID" + i + ")")
//    KeYmaeraInterface.getSubtree(taskId, nId, (p: ProofStepInfo) => { println(p.infos); p.infos.get("tactic") == Some(i.toString) }) match {
//      case Some(s) =>
//        println("Got update " + s)
//        if(proofs.find(MongoDBObject("_id" -> pn.get("_id"))).one == null) {
//          val query = JSON.parse(s).asInstanceOf[DBObject]
//          store(query, pn.get("_id").asInstanceOf[ObjectId])
//        } else {
//          JSON.parse(s).asInstanceOf[DBObject].getAs[MongoDBList]("children") match {
//            case Some(l) => for (c <- store(l)) {
//              val query = $push("children" -> c)
//              val org = MongoDBObject("_id" -> pn.get("_id"))
//              proofs.update(org, query, true)
//            }
//            case None => println("No children")
//          }
//        }
//        f(s)
//      case None => println("did not find subtree")
//    }
//  }
//
//  private def printJSON(o: DBObject): String = {
//    "{ " +
//      (o.keys.map( key => {
//        if (key == "children")
//          "\"children\": [ " + (for(c <- o.getAs[MongoDBList](key).get) yield printJSON(proofs.find(MongoDBObject("_id" -> new ObjectId(c.toString))).one)).mkString(", ") + " ]"
//        else if(key == "sequent")
//          "\"" + key + "\":" + o(key).toString
//        else if(key == "model")
//          "\"" + key + "\":" + printJSON(proofs.find(MongoDBObject("_id" -> o(key))).one)
//        else if(key == "_id")
//          "\"" + key + "\":\"" + o(key).asInstanceOf[ObjectId].toHexString + "\""
//        else
//          "\"" + key + "\":\"" + o(key).toString + "\""
//      })
//      ).mkString(", ") + "}"
//  }
//
//  def getSubtree(pnId: String): String = {
//    val pn = proofs.find(MongoDBObject("_id" -> new ObjectId(pnId)))
//    if(pn != null && pn.one != null) {
//      printJSON(pn.one)
//    } else {
//      val pn = models.find(MongoDBObject("_id" -> new ObjectId(pnId)))
//      if(pn != null && pn.one != null)
//        printJSON(pn.one)
//      else "{}"
//    }
//  }
//
//  def getModel(pnId: String): String = {
//    if (pnId == null) {
//      "{}"
//    }
//    else {
//      val pn = models.find(MongoDBObject("_id" -> new ObjectId(pnId)))
//      if (pn != null && pn.one != null)
//        printJSON(pn.one)
//      else "{}"
//    }
//  }
//
//}
