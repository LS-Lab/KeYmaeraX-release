/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.configuration

import org.keymaerax.hydra.Response
import spray.json.{JsFalse, JsObject, JsString, JsTrue, JsValue}

class ConfigureZ3Response(z3Path: String, success: Boolean) extends Response {
  def getJson: JsValue = JsObject("z3Path" -> JsString(z3Path), "success" -> { if (success) JsTrue else JsFalse })
}
