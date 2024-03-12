/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.models

import edu.cmu.cs.ls.keymaerax.hydra.{ModelPOJO, Response}
import spray.json.{JsObject, JsString, JsValue}

class GetModelTacticResponse(model: ModelPOJO) extends Response {
  def getJson: JsValue = JsObject(
    "modelId" -> JsString(model.modelId.toString),
    "modelName" -> JsString(model.name),
    "tacticBody" -> JsString(model.tactic.getOrElse("")),
  )
}
