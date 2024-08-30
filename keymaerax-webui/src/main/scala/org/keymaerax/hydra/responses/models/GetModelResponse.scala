/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.models

import org.keymaerax.GlobalState
import org.keymaerax.hydra.{ModelPOJO, Response}
import org.keymaerax.parser.{ArchiveParser, ParseException}
import spray.json.{JsArray, JsBoolean, JsNumber, JsObject, JsString, JsValue}

class GetModelResponse(model: ModelPOJO) extends Response {

  private def illustrationLinks(): List[String] =
    try { GlobalState.archiveParser(model.keyFile).flatMap(_.info.get("Illustration")) }
    catch { case _: ParseException => Nil }

  def getJson: JsValue = JsObject(
    "id" -> JsString(model.modelId.toString),
    "name" -> JsString(model.name),
    "date" -> JsString(model.date),
    "description" -> JsString(model.description),
    "illustrations" -> JsArray(illustrationLinks().map(JsString(_)).toVector),
    "pubLink" -> JsString(model.pubLink),
    "keyFile" -> JsString(model.keyFile),
    "title" -> JsString(model.title),
    "hasTactic" -> JsBoolean(model.tactic.isDefined),
    "tactic" -> JsString(model.tactic.getOrElse("")),
    "numAllProofSteps" -> JsNumber(model.numAllProofSteps),
    "isExercise" -> JsBoolean(ArchiveParser.isExercise(model.keyFile)),
  )
}
