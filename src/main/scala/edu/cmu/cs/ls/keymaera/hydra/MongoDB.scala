package edu.cmu.cs.ls.keymaera.hydra
import com.mongodb.casbah.Imports._
import edu.cmu.cs.ls.keymaera.api.KeYmaeraInterface
import edu.cmu.cs.ls.keymaera.core.{ProofStepInfo, ProofNodeInfo}
import org.bson.BSONObject
import com.mongodb.util.JSON
import org.bson.types.ObjectId
import edu.cmu.cs.ls.keymaera.tactics.Tactics

/**
 * Created by jdq on 6/12/14.
 */
object MongoDB {
  val mongoClient = MongoClient("localhost", 27017)
  val proofs = mongoClient("keymaera")("proofs")
  val tactics = mongoClient("keymaera")("tactics")
  val positionTactics = mongoClient("keymaera")("positionTactics")
  val models = mongoClient("keymaera")("models")

  initTactics

  // FIXME: in the long run this should only make sure that the database state is consistent
  proofs.dropCollection
  tactics.dropCollection
  positionTactics.dropCollection
  models.dropCollection

  //FIXME in the long run we need to save everything in the database to restart KeYmaera
  def initTactics =
    for((i, s) <- KeYmaeraInterface.getTactics)
      tactics.insert(MongoDBObject("tacticId" -> i, "name" -> s))

  def getTactic(i: Int): String = tactics.find(MongoDBObject("tacticId" -> i)).one.get("_id").toString


  /**
   * Add a new model to the database. This will return a unique identifier for this model.
   * Each model will have a parser status in the database
   *
   * @param content the content to be added to the database which will be parsed by KeYmaera
   * @param callback the callback function will be called once the parsing by KeYmaera has finished and thus the
   *                 parsing status is consistent within the database
   * @return a unique identifier for the model
   */
  def addModel(content: String, callback: String => Unit): String = {
    val query = MongoDBObject("parserResult" -> "unknown")
    models += query
    val ins = models.find(query).one
    println("Result is " + ins)
    ins.get("_id") match {
      case id: ObjectId =>
        try {
          val (tId, model) = KeYmaeraInterface.addTask(content)
          println("Parsed " + model)
          val jsonModel = JSON.parse(model)
          models.update(MongoDBObject("_id" -> id), $set("parserResult" -> "success", "taskId" -> tId, "nodeId" -> tId, "model" -> jsonModel))
        } catch {
          case e: Exception => models.update(MongoDBObject("_id" -> id), $set("parserResult" -> "failed", "reason" -> (e.getClass + ": " + e.getMessage + "\n" + e.getStackTraceString)))
        }
      case a => throw new IllegalStateException("Writing to database did not return a valid ObjectID. Got: " + a)
    }
    val res = ins.get("_id").toString
    callback(res)
    res
  }

  /**
   * This API call is used to dispatch a tactic. It will return true if the tactic has been dispatched successfully
   * and false otherwise. Once the tactic has been completed all its results will become visible in the database.
   *
   * @param tacticId
   * @param pnId
   * @return
   */
  def runTactic(tacticId: String, pnId: String): Boolean = {
    val tactic = tactics.find(MongoDBObject("_id" -> new ObjectId(tacticId)))
    val pn = models.find(MongoDBObject("_id" -> new ObjectId(pnId)))
    require(tactic.length == 1 && pn.length == 1, "tactic.length = " + tactic.length + " should be 1 and pn.length should be 1 but is " + pn.length)
    tactic.one()
    val t = tactic.one
    val node = pn.one
    (node.get("taskId"), node.get("nodeId"), t.get("tacticId")) match {
      case (tId: Integer, nId, tacId: Integer) =>
        KeYmaeraInterface.runTactic(tId, Some(nId.toString), tacId, Some(tacticCompleted(node)))
        true
      case _ => false
    }
  }

  private def tacticCompleted(pn: BSONObject)(i: Int)(taskId: Int, nId: Option[String], tacticId: Int) {
    println("Tactic completed " + tacticId)
    KeYmaeraInterface.getSubtree(taskId, nId, (p: ProofStepInfo) => { println(p.infos); p.infos.get("tactic") == Some(i.toString) }) match {
      case Some(s) =>
        // TODO search pn in the proofs data structure (insert if it does not yet exist) then add the subtree to it
        // replace the node by the subtree
        println("Got update " + s)
        //FIXME This will replace all prior proof nodes. This causes trouble if there are alternative tactics running on the same node.
        proofs.insert(MongoDBObject("_id" -> pn.get("_id")), JSON.parse(s).asInstanceOf[DBObject])
      case None => println("did not find subtree")
    }
  }

  def getSubtree(pnId: String): String = {
    val pn = proofs.find(MongoDBObject("_id" -> pnId))
    pn.one.toString
  }


}
