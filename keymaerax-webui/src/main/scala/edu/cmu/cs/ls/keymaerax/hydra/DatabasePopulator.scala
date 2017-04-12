package edu.cmu.cs.ls.keymaerax.hydra

import java.util.Calendar

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, Interpreter, SequentialInterpreter, SpoonFeedingInterpreter}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXArchiveParser, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.tacticsinterface.TraceRecordingListener
import spray.json._
import spray.json.DefaultJsonProtocol._

import scala.collection.immutable._

/**
  * Populates the database from a JSON collection of models and tactics.
  * @author Stefan Mitsch
  */
object DatabasePopulator {

  //@todo publish the tutorials and case studies somewhere on the web page, add Web UI functionality to explore tutorials
  // and case studies and import into the database

  case class TutorialEntry(name: String, model: String, description: Option[String], title: Option[String],
                           link: Option[String], tactic: Option[(String, String, Boolean)])

  /** Imports tutorial entries from the JSON file at URL. Optionally proves the models when tactics are present. */
  def importJson(db: DBAbstraction, user: String, url: String, prove: Boolean = false): Unit = {
    readTutorialEntries(url).foreach(importModel(db, user, prove))
  }

  /** Reads a .kya archive from the URL `url` as tutorial entries (i.e., one tactic per entry). */
  def readKya(url: String): List[TutorialEntry] = {
    val kya = loadResource(url)
    val archiveEntries = KeYmaeraXArchiveParser.read(kya)
    archiveEntries.flatMap({case (modelName, modelContent, tactics) =>
      tactics.map({case (tname, tactic) => TutorialEntry(modelName, modelContent, None, None, None, Some((tname, tactic, true)))})})
  }

  /** Reads tutorial entries from the specified URL. */
  def readTutorialEntries(url: String): List[TutorialEntry] = {
    val json = loadResource(url)
    val modelRepo = json.parseJson.asJsObject
    val entries: JsArray = modelRepo.fields("entries").asInstanceOf[JsArray]
    entries.elements.map(_.asJsObject)
      .map(e => TutorialEntry(
        e.fields("name").asInstanceOf[JsString].value,
        loadResource(e.fields("model").asInstanceOf[JsString].value),
        getOptionalField(e, "description", _.convertTo[String]),
        getOptionalField(e, "title", _.convertTo[String]),
        getOptionalField(e, "link", _.convertTo[String]),
        getOptionalField[String](e, "tactic", v=>loadResource(v.convertTo[String])).map(
          t => ("", t, getOptionalField(e, "proves", _.convertTo[Boolean]).getOrElse(true)))))
      .toList
  }

  /** Gets the value of an optional field in object `o`. */
  private def getOptionalField[A](o: JsObject, fieldName: String, converter: JsValue => A): Option[A] = {
    if (o.fields.contains(fieldName)) Some(converter(o.fields(fieldName)))
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
  def importModel(db: DBAbstraction, user: String, prove: Boolean)(entry: TutorialEntry): Unit = {
    val now = Calendar.getInstance()
    if (!db.getModelList(user).exists(_.name == entry.name)) {
      println("Importing model " + entry.name + "...")
      db.createModel(user, entry.name, entry.model, now.getTime.toString, entry.description,
        entry.link, entry.title, entry.tactic match { case Some((_, t, _)) => Some(t) case _ => None }) match {
        case Some(modelId) => entry.tactic match {
          case Some((tname, tacticText, _)) =>
            println("Importing proof...")
            val proofId = db.createProofForModel(modelId, entry.name + " (" + tname + ")", "Imported from tactic " + tname,
              now.getTime.toString, Some(tacticText))
            if (prove) executeTactic(db, entry.model, proofId, tacticText)
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

  /** Prepares an interpreter for executing tactics. */
  def prepareInterpreter(db: DBAbstraction, proofId: Int): Interpreter = {
    def listener(proofId: Int)(tacticName: String, parentInTrace: Int, branch: Int) = {
      val trace = db.getExecutionTrace(proofId, withProvables=false)
      assert(-1 <= parentInTrace && parentInTrace < trace.steps.length, "Invalid trace index " + parentInTrace + ", expected -1<=i<trace.length")
      val parentStep: Option[Int] = if (parentInTrace < 0) None else Some(trace.steps(parentInTrace).stepId)
      val globalProvable = parentStep match {
        case None => db.getProvable(db.getProofInfo(proofId).provableId.get).provable
        case Some(sId) => db.getExecutionStep(proofId, sId).map(_.local).get
      }
      new TraceRecordingListener(db, proofId, parentStep,
        globalProvable, branch, recursive = false, tacticName) :: Nil
    }
    SpoonFeedingInterpreter(proofId, db.createProof, listener, SequentialInterpreter)
  }

  /** Executes the `tactic` on the `model` and records the tactic steps as proof in the database. */
  def executeTactic(db: DBAbstraction, model: String, proofId: Int, tactic: String): Unit = {
    val interpreter = prepareInterpreter(db, proofId)
    val parsedTactic = BelleParser(tactic)
    interpreter(parsedTactic, BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(model))))
  }

}
