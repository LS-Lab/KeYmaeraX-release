/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.modelplex

import edu.cmu.cs.ls.keymaerax.core.Variable
import edu.cmu.cs.ls.keymaerax.hydra.{ModelPOJO, Response}
import spray.json.{JsArray, JsObject, JsString, JsValue}

class ModelPlexMandatoryVarsResponse(model: ModelPOJO, vars: Set[Variable]) extends Response {
  def getJson: JsValue = JsObject(
    "modelid" -> JsString(model.modelId.toString),
    "mandatoryVars" -> JsArray(vars.map(v => JsString(v.prettyString)).toVector),
  )
}
