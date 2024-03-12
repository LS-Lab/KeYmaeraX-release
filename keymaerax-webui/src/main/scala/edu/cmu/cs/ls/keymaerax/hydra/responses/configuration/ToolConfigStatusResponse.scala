/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.configuration

import edu.cmu.cs.ls.keymaerax.hydra.Response
import spray.json.{JsFalse, JsObject, JsString, JsTrue, JsValue}

class ToolConfigStatusResponse(tool: String, configured: Boolean) extends Response {
  def getJson: JsValue = JsObject("tool" -> JsString(tool), "configured" -> { if (configured) JsTrue else JsFalse })
}
