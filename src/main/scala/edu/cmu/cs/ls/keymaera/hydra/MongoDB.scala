package edu.cmu.cs.ls.keymaera.hydra
import com.mongodb.casbah.Imports._

/**
 * Created by jdq on 6/12/14.
 */
object MongoDB {
  val mongoClient = MongoClient("localhost", 27017)
  val proofs = mongoClient("keymaera")("proofs")
  val tactics = mongoClient("keymaera")("tactics")
  val models = mongoClient("keymaera")("models")

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
    val id: String = models.insert(query) match {
      case id: ObjectId => id.toHexString
      case _ => throw new IllegalStateException("Writing to database did not return a valid ObjectID")
    }
    try {
      val pn = KeYmaeraInterface.parseProblem(content)
      models.update(MongoDBObject("_id" -> id), $set("parserResult" -> "success"))
      // TODO how do we now store the pointer to the ProofNode in the DB?
    } catch {
      case e: Exception => models.update(MongoDBObject("_id" -> id), $set("parserResult" -> e.getMessage))
    }
    id
  }


}
