/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.tools

import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.hydra.Response
import spray.json.{JsArray, JsObject, JsString, JsValue}

class ODEConditionsResponse(sufficient: List[Formula], necessary: List[Formula]) extends Response {
  // @todo formula JSON with HTML formatting in UI
  override def getJson: JsValue = JsObject(
    "sufficient" -> JsArray(sufficient.map(f => JsObject("text" -> JsString(f.prettyString))).toVector),
    "necessary" -> JsArray(necessary.map(f => JsObject("text" -> JsString(f.prettyString))).toVector),
  )
}
