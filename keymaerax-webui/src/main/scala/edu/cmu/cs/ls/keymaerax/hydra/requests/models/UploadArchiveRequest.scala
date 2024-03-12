/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.models

import edu.cmu.cs.ls.keymaerax.hydra.DatabasePopulator.TutorialEntry
import edu.cmu.cs.ls.keymaerax.hydra.responses.models.{ModelUploadResponse, ParseErrorResponse}
import edu.cmu.cs.ls.keymaerax.hydra.{
  BooleanResponse,
  DBAbstraction,
  DatabasePopulator,
  Response,
  UserRequest,
  WriteRequest,
}
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, ParseException}

import scala.collection.immutable.{List, Nil}

class UploadArchiveRequest(db: DBAbstraction, userId: String, archiveText: String, modelName: Option[String])
    extends UserRequest(userId, _ => true) with WriteRequest {
  def resultingResponses(): List[Response] = {
    try {
      val parsedArchiveEntries = ArchiveParser.parse(archiveText)

      // @note archive parser augments a plain formula with definitions and flags it with name '<undefined>'
      val archiveEntries =
        if (parsedArchiveEntries.size == 1 && parsedArchiveEntries.head.name == "<undefined>") {
          parsedArchiveEntries.head.copy(name = modelName.getOrElse("undefined")) :: Nil
        } else parsedArchiveEntries

      val (failedModels, succeededModels) = archiveEntries
        .foldLeft((List[String](), List[(String, Int)]()))({ case ((failedImports, succeededImports), entry) =>
          val result = DatabasePopulator
            .importModel(db, userId, prove = false)(DatabasePopulator.toTutorialEntry(entry))
          (failedImports ++ result.toSeq, succeededImports ++ result.left.toSeq)
        })
      if (failedModels.isEmpty) {
        if (archiveEntries.size == 1) { ModelUploadResponse(Some(succeededModels.head._2.toString), None) :: Nil }
        else BooleanResponse(flag = true) :: Nil
      } else throw new Exception(
        "Failed to import the following models\n" + failedModels.mkString("\n") + "\nSucceeded importing:\n" +
          succeededModels.mkString("\n") +
          "\nModel import may have failed because of model name clashed. Try renaming the failed models in the archive to names that do not yet exist in your model list."
      )
    } catch {
      // @todo adapt parse error positions (are relative to problem inside entry)
      case e: ParseException =>
        val entryName = """(Theorem|Lemma|ArchiveEntry|Exercise)\s*"(?<name>[^"]*)""""
          .r
          .findFirstMatchIn(archiveText)
          .map(_.group("name"))
          .getOrElse("<anonymous>")

        val entry = TutorialEntry(entryName, archiveText, None, None, None, List.empty)
        DatabasePopulator.importModel(db, userId, prove = false)(entry) match {
          case Left((_, id)) => ModelUploadResponse(Some(id.toString), Some(e.getMessage)) :: Nil
          case _ => ParseErrorResponse(e.msg, e.expect, e.found, e.getDetails, e.loc, e) :: Nil
        }
    }
  }
}
