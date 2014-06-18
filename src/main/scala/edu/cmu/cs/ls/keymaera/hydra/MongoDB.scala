package edu.cmu.cs.ls.keymaera.hydra
import com.mongodb.casbah.Imports._
import edu.cmu.cs.ls.keymaera.api.KeYmaeraInterface
import edu.cmu.cs.ls.keymaera.core.{ProofStepInfo, ProofNodeInfo}
import org.bson.BSONObject

/**
 * Created by jdq on 6/12/14.
 */
object MongoDB {
  val mongoClient = MongoClient("localhost", 27017)
  val proofs = mongoClient("keymaera")("proofs")
  val tactics = mongoClient("keymaera")("tactics")
  val models = mongoClient("keymaera")("models")

  initTactics

  //FIXME in the long run we need to save everything in the database to restart KeYmaera
  def initTactics =
    for((i, s) <- KeYmaeraInterface.getTactics)
      tactics.insert(MongoDBObject("tacticId" -> i, "name" -> s))


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
    val id: String = models.insert(query).getUpsertedId match {
      case id: ObjectId =>
        try {
          val (tId, model) = KeYmaeraInterface.addTask(content)
          models.update(MongoDBObject("_id" -> id), $set("parserResult" -> "success", "taskId" -> tId, "nodeId" -> tId, "model" -> model))
        } catch {
          case e: Exception => models.update(MongoDBObject("_id" -> id), $set("parserResult" -> e.getMessage))
        }
        id.toHexString
      case _ => throw new IllegalStateException("Writing to database did not return a valid ObjectID")
    }
    id
  }

  def runTactic(tacticId: String, pnId: String): Boolean = {
    val tactic = tactics.find(MongoDBObject("_id" -> tacticId))
    val pn = models.find(MongoDBObject("_id" -> pnId))
    require(tactic.length == 1 && pn.length == 1)
    tactic.one()
    val t = tactic.one
    val node = pn.one
    (node.get("taskId"), node.get("nodeId"), t.get("tacticId")) match {
      case (tId: Integer, nId: String, tacId: Integer) =>
        KeYmaeraInterface.runTactic(tId, Some(nId), tacId, Some(tacticCompleted(node)))
        true
      case _ => false
    }
  }

  private def tacticCompleted(pn: BSONObject)(taskId: Int, nId: Option[String], tacticId: Int) {
    KeYmaeraInterface.getSubtree(taskId, nId, (p: ProofStepInfo) => p.infos.get("tactic") == Some(tacticId.toString)) match {
      case Some(s) => // TODO: search pn in the proofs data structure (insert if it does not yet exist) then add the subtree to it
      case None =>
    }
  }


}
