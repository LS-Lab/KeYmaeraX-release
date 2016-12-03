package edu.cmu.cs.ls.keymaerax.hydra

import java.util.Calendar

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, SequentialInterpreter, SpoonFeedingInterpreter}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import edu.cmu.cs.ls.keymaerax.tacticsinterface.TraceRecordingListener

import spray.json._

import scala.collection.immutable._

/**
  * Populates the database from a JSON collection of models and tactics.
  * @author Stefan Mitsch
  */
object DatabasePopulator {

  //@todo publish the tutorials and case studies somewhere on the web page, add Web UI functionality to explore tutorials
  // and case studies and import into the database

  def importJson(db: DBAbstraction, user: String, url: String, prove: Boolean = false) = {
    val json = loadResource(url)
    val modelRepo = json.parseJson.asJsObject
    val entries: JsArray = modelRepo.fields("entries").asInstanceOf[JsArray]
    entries.elements.map(_.asJsObject).foreach(e =>
      importModel(db, user,
        e.fields("name").asInstanceOf[JsString].value,
        loadResource(e.fields("model").asInstanceOf[JsString].value),
        getOptionalField(e, "description"),
        getOptionalField(e, "title"),
        getOptionalField(e, "tactic", loadResource),
        getOptionalField(e, "link"),
        prove))
  }

  /** Gets the string value of an optional field in object `o`. */
  private def getOptionalField(o: JsObject, fieldName: String, converter: String => String = s=>s): Option[String] = {
    if (o.fields.contains(fieldName)) Some(converter(o.fields(fieldName).asInstanceOf[JsString].value))
    else None
  }

  /** Loads the specified resource, either from the JAR if URL starts with 'classpath:' or from the URL. */
  private def loadResource(url: String): String =
    if (url.startsWith("classpath:")) {
      io.Source.fromInputStream(getClass.getResourceAsStream(url.substring("classpath:".length))).mkString
    } else {
      io.Source.fromURL(url).mkString
    }



  /** Imports a model with info into the database; optionally records a proof obtained using `tactic`. */
  def importModel(db: DBAbstraction, user: String, modelName: String, model: String,
                  description: Option[String], title: Option[String], tactic: Option[String], link: Option[String],
                  prove: Boolean) = {
    val now = Calendar.getInstance()
    if (!db.getModelList(user).exists(_.name == modelName)) {
      println("Importing model " + modelName + "...")
      db.createModel(user, modelName, model, now.getTime.toString, description, link, title, tactic) match {
        case Some(modelId) => tactic match {
          case Some(tacticText) if prove =>
            println("Importing proof...")
            val proofId = db.createProofForModel(modelId, modelName + " proof", "Imported from tactic", now.getTime.toString)
            executeTactic(db, model, proofId, tacticText)
            println("...done")
          case _ => // nothing else to do, not asked to prove or don't know how to prove without tactic
        }
        case None => ???
      }
      println("...done")
    } else {
      println("WARNING: trying to import model that already exists in DB --> skipping import")
    }
  }

  /** Executes the `tactic` on the `model` and records the tactic steps as proof in the database. */
  def executeTactic(db: DBAbstraction, model: String, proofId: Int, tactic: String) = {
    def listener(tacticName: String, branch: Int) = {
      val trace = db.getExecutionTrace(proofId)
      val globalProvable = trace.lastProvable
      new TraceRecordingListener(db, proofId, trace.executionId.toInt, trace.lastStepId,
        globalProvable, trace.alternativeOrder, branch, recursive = false, tacticName) :: Nil
    }
    val interpreter = SpoonFeedingInterpreter(listener, SequentialInterpreter)
    val parsedTactic = BelleParser(tactic)
    interpreter(parsedTactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(model))))
  }

}
