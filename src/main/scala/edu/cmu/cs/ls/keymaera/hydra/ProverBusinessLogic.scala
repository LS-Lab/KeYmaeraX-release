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
object ProverBusinessLogic {
  val mongoClient = MongoClient("localhost", 27017)
  val proofs = mongoClient("keymaera")("proofs")
  val tactics = mongoClient("keymaera")("tactics")
  val positionTactics = mongoClient("keymaera")("positionTactics")
  val models = mongoClient("keymaera")("models")


  // FIXME: in the long run this should only make sure that the database state is consistent
  proofs.dropCollection
  tactics.dropCollection
  positionTactics.dropCollection
  models.dropCollection

  initTactics

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
   * @return a unique identifier for the model
   */
  def addModel(content: String): String = {
      val (tId, model) = KeYmaeraInterface.addTask(content)
      println("Parsed " + model)
      val jsonModel = JSON.parse(model)
      val query = MongoDBObject("taskId" -> tId, "nodeId" -> tId, "model" -> jsonModel)
      models += query
      val ins = models.find(query).one
      println("Result is " + ins)
      ins.get("_id").toString
  }

  /**
   * This API call is used to dispatch a tactic. It will return true if the tactic has been dispatched successfully
   * and false otherwise. Once the tactic has been completed all its results will become visible in the database.
   *
   * @param tacticId
   * @param pnId
   * @return
   */
  def runTactic(tacticId: String, pnId: String, nId: String, callback: String => Unit = _ => ()): Boolean = {
    println("Run tactic called")
    val tactic = tactics.find(MongoDBObject("_id" -> new ObjectId(tacticId)))
    println("Tactic is " + tactic)
    val qry = models.find(MongoDBObject("_id" -> new ObjectId(pnId)))
    val node = if(qry == null || qry.one == null)
      proofs.find(MongoDBObject("_id" -> new ObjectId(pnId))).one
      else qry.one
    println("Node is " + node)
    require(tactic.length == 1, "tactic.length = " + tactic.length + " should be 1")
    val t = tactic.one
    (node.get("taskId"), t.get("tacticId")) match {
      case (tId: Integer, tacId: Integer) =>
        println("Actually running tactic on node " + nId)
        KeYmaeraInterface.runTactic(tId, Some(nId), tacId, Some(tacticCompleted(callback, node)))
        true
      case _ => false
    }
  }

  private def tacticCompleted(f: String => Unit, pn: BSONObject)(i: Int)(taskId: Int, nId: Option[String], tacticId: Int) {
    println("Tactic completed " + tacticId)
    KeYmaeraInterface.getSubtree(taskId, nId, (p: ProofStepInfo) => { println(p.infos); p.infos.get("tactic") == Some(i.toString) }) match {
      case Some(s) =>
        // TODO search pn in the proofs data structure (insert if it does not yet exist) then add the subtree to it
        // replace the node by the subtree
        println("Got update " + s)
        //FIXME This will replace all prior proof nodes. This causes trouble if there are alternative tactics running on the same node.
        val query = JSON.parse(s).asInstanceOf[DBObject]
        val org = MongoDBObject("_id" -> pn.get("_id"))
        proofs.update(org, query, true)
        f(s)
      case None => println("did not find subtree")
    }
  }

  def getSubtree(pnId: String): String = {
    val pn = proofs.find(MongoDBObject("_id" -> new ObjectId(pnId)))
    if(pn != null && pn.one != null)
      pn.one.toString
    else {
      val pn = models.find(MongoDBObject("_id" -> new ObjectId(pnId)))
      if(pn != null && pn.one != null)
        pn.one.toString
      else "{}"
    }
  }


}
