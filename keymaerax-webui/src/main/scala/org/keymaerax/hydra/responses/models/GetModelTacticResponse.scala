/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.models

import org.keymaerax.hydra.{ModelPOJO, Response}
import spray.json.{JsObject, JsString, JsValue}

class GetModelTacticResponse(model: ModelPOJO) extends Response {
  def getJson: JsValue = JsObject(
    "modelId" -> JsString(model.modelId.toString),
    "modelName" -> JsString(model.name),
    "tacticBody" -> JsString(model.tactic.getOrElse("")),
  )
}
