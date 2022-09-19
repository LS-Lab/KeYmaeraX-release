/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.responses.models

import edu.cmu.cs.ls.keymaerax.hydra.{ModelPOJO, Response}
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import spray.json.{JsArray, JsBoolean, JsNull, JsNumber, JsObject, JsString, JsValue}

class ModelListResponse(models: List[ModelPOJO]) extends Response {
  val objects: List[JsObject] = models.map(modelpojo => JsObject(
    "id" -> JsString(modelpojo.modelId.toString),
    "name" -> JsString(modelpojo.name),
    "date" -> JsString(modelpojo.date),
    "description" -> JsString(modelpojo.description),
    "pubLink" -> JsString(modelpojo.pubLink),
    "keyFile" -> JsString(modelpojo.keyFile),
    "title" -> JsString(modelpojo.title),
    "hasTactic" -> JsBoolean(modelpojo.tactic.isDefined),
    "numAllProofSteps" -> JsNumber(modelpojo.numAllProofSteps),
    "isExercise" -> JsBoolean(ArchiveParser.isExercise(modelpojo.keyFile)),
    "folder" -> (if (modelpojo.name.contains("/")) JsString(modelpojo.name.substring(0, modelpojo.name.indexOf('/'))) else JsNull)
  ))

  def getJson: JsValue = JsArray(objects:_*)
}