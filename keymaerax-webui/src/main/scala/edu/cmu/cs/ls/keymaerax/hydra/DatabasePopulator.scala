/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra

import java.util.Calendar
import edu.cmu.cs.ls.keymaerax.Logging
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, Declaration, ParsedArchiveEntry}
import edu.cmu.cs.ls.keymaerax.tacticsinterface.TraceRecordingListener
import spray.json._
import spray.json.DefaultJsonProtocol._

import scala.annotation.tailrec
import scala.collection.immutable._
import scala.util.Try

/**
  * Populates the database from a JSON collection of models and tactics.
  * @author Stefan Mitsch
  */
object DatabasePopulator extends Logging {

  //@todo publish the tutorials and case studies somewhere on the web page, add Web UI functionality to explore tutorials
  // and case studies and import into the database

  private val GITHUB_PROJECTS_RAW_PATH = "https://raw.githubusercontent.com/LS-Lab/KeYmaeraX-projects/master"

  case class TutorialEntry(name: String, model: String, description: Option[String], title: Option[String],
                           link: Option[String], tactic: List[(String, String, Boolean)], kind: String = "Unknown")

  /** Succeeded imports: model name and created Id, failed: model name. */
  case class ImportResult(succeeded: List[(String, Int)], failed: List[String])

  /** Imports an archive from URL. Optionally proves the models when tactics are present. */
  def importKya(db: DBAbstraction, user: String, url: String, prove: Boolean, exclude: List[ModelPOJO]): ImportResult = {
    val result = readKyx(url)
      .filterNot(e => exclude.exists(_.name == e.name))
      .map(DatabasePopulator.importModel(db, user, prove = false))
    ImportResult(result.flatMap(_.left.toOption), result.flatMap(_.right.toOption))
  }

  /** Reads a .kyx archive from the URL `url` as tutorial entries (i.e., one tactic per entry). */
  def readKyx(url: String): List[TutorialEntry] = {
    val entries = url.split('#').toList match {
      case contentUrl :: Nil => ArchiveParser.parse(loadResource(contentUrl))
      case contentUrl :: entryName :: Nil =>
        ArchiveParser.getEntry(entryName, loadResource(contentUrl)).
          getOrElse(throw new IllegalArgumentException("Unknown archive entry " + entryName)) :: Nil
      case _ => throw new IllegalArgumentException("Entry URLs are allowed to contain at most 1 '#', but got " + url)
    }
    entries.map(toTutorialEntry)
  }

  /** Converts a parsed archive entry into a tutorial entry as expected by this importer. */
  def toTutorialEntry(entry: ParsedArchiveEntry): TutorialEntry = {
    TutorialEntry(entry.name, entry.fileContent, entry.info.get("Description"), entry.info.get("Title"),
      entry.info.get("Link"), entry.tactics.map({ case (tname, tacticContent, _) => (tname, tacticContent, true) }),
      entry.kind)
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
          t => ("", t, getOptionalField(e, "proves", _.convertTo[Boolean]).getOrElse(true))).toList))
      .toList
  }

  /** Gets the value of an optional field in object `o`. */
  private def getOptionalField[A](o: JsObject, fieldName: String, converter: JsValue => A): Option[A] = {
    if (o.fields.contains(fieldName)) Some(converter(o.fields(fieldName)))
    else None
  }

  /** Loads the specified resource, either from the JAR if URL starts with 'classpath:' or from the URL. */
  @tailrec
  def loadResource(url: String): String =
    if (url.startsWith("classpath:")) {
      val resource = getClass.getResourceAsStream(url.substring("classpath:".length))
      if (resource != null) io.Source.fromInputStream(resource, edu.cmu.cs.ls.keymaerax.core.ENCODING).mkString
      else if (url.startsWith("classpath:/keymaerax-projects")) loadResource(GITHUB_PROJECTS_RAW_PATH + url.substring("classpath:/keymaerax-projects".length))
      else throw new Exception(s"Example '$url' neither included in build nor available in projects repository")
    } else if (url.startsWith("file://")) {
      val path = url.stripPrefix("file://")
      val source = io.Source.fromFile(path, edu.cmu.cs.ls.keymaerax.core.ENCODING)
      try source.mkString finally source.close()
    } else {
      val source = io.Source.fromURL(url, edu.cmu.cs.ls.keymaerax.core.ENCODING)
      try source.mkString finally source.close()
    }

  /** Imports a model with info into the database; optionally records a proof obtained using `tactic`.
    * Returns Left(modelName, ID) on success, Right(modelName) on failure */
  def importModel(db: DBAbstraction, user: String, prove: Boolean)(entry: TutorialEntry): Either[(String, Int), String] = {
    val now = Calendar.getInstance()

    def doImport(entry: TutorialEntry): Either[(String, Int), String] = {
      logger.info("Importing model " + entry.name + "...")
      val result = db.createModel(user, entry.name, entry.model, now.getTime.toString, entry.description,
        entry.link, entry.title, entry.tactic.headOption.map(_._2)) match {
        case Some(modelId) =>
          entry.tactic.foreach({ case (tname, ttext, _) =>
            logger.info("Importing proof...")
            val proofId = db.createProofForModel(modelId, tname, "Proof from archive", now.getTime.toString, Some(ttext))
            if (prove) executeTactic(db, entry.model, proofId, ttext)
            logger.info("...done")
          })
          Left(entry.name -> modelId)
        case None => Right(entry.name)
      }
      logger.info("...done")
      result
    }

    db.getModelList(user).find(_.name == entry.name) match {
      case Some(e) =>
        if (backupPriorModel(db, user, e, entry)) doImport(entry)
        else Left(e.name -> e.modelId)
      case None => doImport(entry)
    }
  }

  /** Creates a backup if a different model with the same name as `entry` already exists in the database. Returns false
    * if the entry already exists verbatim in the database, true otherwise. */
  private def backupPriorModel(db: DBAbstraction, user: String, oldEntry: ModelPOJO, newEntry: TutorialEntry): Boolean = {
    def createBackup(backupName: String): Unit = {
      db.updateModel(oldEntry.modelId, backupName,
        if (oldEntry.title != "") Some(oldEntry.title) else None,
        if (oldEntry.description != "") Some(oldEntry.description) else None,
        if (oldEntry.keyFile != "") Some(oldEntry.keyFile) else None,
        oldEntry.tactic)
    }

    val backupName = db.getUniqueModelName(user, newEntry.name)
    val oldContent = Try(ArchiveParser.parse(oldEntry.keyFile, parseTactics=false).head).toOption
    val newContent = Try(ArchiveParser.parse(newEntry.model, parseTactics=false).head).toOption
    (oldContent, newContent) match {
      // if entry with same name but different model exists, do import (return true)
      case (None, None) =>
        val changed = oldEntry.keyFile != newEntry.model
        if (changed) createBackup(backupName)
        changed
      case (Some(_), None) =>
        createBackup(backupName)
        true
      case (None, Some(_)) =>
        createBackup(backupName)
        true
      case (Some(o), Some(n)) =>
        // update only on change
        if (o.defs.exhaustiveSubst(o.model) != n.defs.exhaustiveSubst(n.model) || o.tactics != n.tactics) {
          createBackup(backupName)
          true
        } else false // entry exists verbatim in the database, do not re-import
    }
  }

  /** Prepares an interpreter for executing tactics. */
  def prepareInterpreter(db: DBAbstraction, proofId: Int, defs: Declaration, listeners: Seq[IOListener] = Nil): Interpreter = {
    def listener(proofId: Int)(tacticName: String, parentInTrace: Int, branch: Int) = {
      val trace = db.getExecutionTrace(proofId, withProvables=false)
      assert(-1 <= parentInTrace && parentInTrace < trace.steps.length, "Unable to record " + tacticName +
        " because invalid parent trace index " + parentInTrace +
        ", expected -1<=i<" + trace.steps.length + " (trace.length) in\n" +
        trace.steps.map(s => s.rule + "@" + s.stepId).mkString(", "))
      val parentStep: Option[Int] = if (parentInTrace < 0) None else Some(trace.steps(parentInTrace).stepId)
      val globalProvable = parentStep match {
        case None => db.getProvable(db.getProofInfo(proofId).provableId.get).provable
        case Some(sId) => db.getExecutionStep(proofId, sId).map(_.local).get
      }
      new TraceRecordingListener(db, proofId, parentStep,
        globalProvable, branch, recursive = false, tacticName, constructGlobalProvable = false) :: Nil
    }
    def interpreter(orig: Seq[IOListener]) = LazySequentialInterpreter(orig ++ listeners, throwWithDebugInfo = false)
    SpoonFeedingInterpreter(proofId, -1, db.createProof, defs, listener, interpreter, 0, strict=true, convertPending=true, recordInternal=false)
  }

  /** Executes the `tactic` on the `model` and records the tactic steps as proof in the database. */
  def executeTactic(db: DBAbstraction, model: String, proofId: Int, tactic: String): Unit = {
    val entry = ArchiveParser(model).head
    val interpreter = prepareInterpreter(db, proofId, entry.defs)
    val parsedTactic = BelleParser.parseBackwardsCompatible(tactic, entry.defs)
    interpreter(parsedTactic, BelleProvable.plain(ProvableSig.startPlainProof(ArchiveParser.parseAsFormula(model))))
    interpreter.kill()
  }

}
