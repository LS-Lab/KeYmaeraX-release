/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.tools

import org.keymaerax.core.Formula
import org.keymaerax.hydra.{Response, UIAbbreviatingKeYmaeraXPrettyPrinter}
import spray.json.{JsObject, JsString, JsValue}

class SetupSimulationResponse(initial: Formula, stateRelation: Formula) extends Response {
  private val pp = new UIAbbreviatingKeYmaeraXPrettyPrinter()
  def getJson: JsValue = JsObject("initial" -> JsString(pp(initial)), "stateRelation" -> JsString(pp(stateRelation)))
}
