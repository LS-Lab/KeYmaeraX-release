/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.configuration

import org.keymaerax.hydra.Response
import spray.json.{JsObject, JsString, JsValue}

class Z3ConfigurationResponse(z3Path: String) extends Response {
  def getJson: JsValue = JsObject("z3Path" -> JsString(z3Path))
}
