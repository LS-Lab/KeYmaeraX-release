/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.tools

import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.hydra.{Response, UIAbbreviatingKeYmaeraXPrettyPrinter}
import spray.json.{JsObject, JsString, JsValue}

class SetupSimulationResponse(initial: Formula, stateRelation: Formula) extends Response {
  private val pp = new UIAbbreviatingKeYmaeraXPrettyPrinter()
  def getJson: JsValue = JsObject("initial" -> JsString(pp(initial)), "stateRelation" -> JsString(pp(stateRelation)))
}
