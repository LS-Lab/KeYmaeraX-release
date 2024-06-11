/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.models

import edu.cmu.cs.ls.keymaerax.hydra.responses.models.ModelUpdateResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ErrorResponse, Response, UserRequest, WriteRequest}
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, ParseException}

import scala.collection.immutable.{::, Nil}

class UpdateModelRequest(
    db: DBAbstraction,
    userId: String,
    modelId: String,
    name: String,
    title: String,
    description: String,
    content: String,
) extends UserRequest(userId, _ => true) with WriteRequest {
  private def emptyToOption(s: String): Option[String] = if (s.isEmpty) None else Some(s)

  def resultingResponse(): Response = {
    val modelInfo = db.getModel(modelId)
    if (db.getProofsForModel(modelId).forall(_.stepCount == 0)) {
      if (ArchiveParser.isExercise(content)) {
        db.updateModel(
          modelId.toInt,
          name,
          emptyToOption(title),
          emptyToOption(description),
          emptyToOption(content),
          None,
        )
        ModelUpdateResponse(modelId, name, content, emptyToOption(title), emptyToOption(description), None)
      } else
        try {
          ArchiveParser.parse(content) match {
            case e :: Nil =>
              db.updateModel(
                modelId.toInt,
                e.name,
                e.info.get("Title"),
                e.info.get("Description"),
                emptyToOption(e.fileContent),
                e.tactics.headOption.map(_._2),
              )
              ModelUpdateResponse(
                modelId,
                e.name,
                e.problemContent,
                e.info.get("Title"),
                e.info.get("Description"),
                None,
              )
            case e => new ErrorResponse(s"Expected a single entry, but got ${e.size}")
          }
        } catch {
          case e: ParseException =>
            val entryName = """(Theorem|Lemma|ArchiveEntry|Exercise)\s*"(?<name>[^"]*)""""
              .r
              .findFirstMatchIn(content)
              .map(_.group("name"))
              .getOrElse("<anonymous>")

            db.updateModel(
              modelId.toInt,
              entryName,
              emptyToOption(modelInfo.title),
              emptyToOption(modelInfo.description),
              emptyToOption(content),
              modelInfo.tactic,
            )
            ModelUpdateResponse(
              modelId,
              entryName,
              content,
              emptyToOption(modelInfo.title),
              emptyToOption(modelInfo.description),
              Some(e.msg),
            )
        }
    } else
      new ErrorResponse(s"Unable to update model $modelId because it has ${modelInfo.numAllProofSteps} proof steps")
  }
}
