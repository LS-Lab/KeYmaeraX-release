/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.responses.configuration

import edu.cmu.cs.ls.keymaerax.hydra.Response
import spray.json.{JsObject, JsString, JsValue}

class Z3ConfigSuggestionResponse(defaultPath: String) extends Response {
  def getJson: JsValue = JsObject("z3Path" -> JsString(defaultPath))
}
