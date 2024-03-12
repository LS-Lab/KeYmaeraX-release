/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.models

import edu.cmu.cs.ls.keymaerax.hydra.Response
import spray.json.{JsBoolean, JsObject, JsString, JsValue}

case class ModelUploadResponse(modelId: Option[String], errorText: Option[String]) extends Response {
  def getJson: JsValue = JsObject(
    "success" -> JsBoolean(modelId.isDefined),
    "errorText" -> JsString(errorText.getOrElse("")),
    "modelId" -> JsString(modelId.getOrElse("")),
  )
}
