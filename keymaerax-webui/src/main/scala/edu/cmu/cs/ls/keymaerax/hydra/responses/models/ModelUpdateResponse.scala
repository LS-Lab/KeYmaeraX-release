/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.responses.models

import edu.cmu.cs.ls.keymaerax.hydra.Response
import spray.json.{JsBoolean, JsObject, JsString, JsValue}

case class ModelUpdateResponse(modelId: String, name: String, content: String, title: Option[String], description: Option[String], errorText: Option[String]) extends Response {
  def getJson: JsValue = JsObject(
    "success" -> JsBoolean(errorText.isEmpty),
    "errorText" -> JsString(errorText.getOrElse("")),
    "modelId" -> JsString(modelId),
    "name" -> JsString(name),
    "content" -> JsString(content),
    "title" -> JsString(title.getOrElse("")),
    "description" -> JsString(description.getOrElse(""))
  )
}
