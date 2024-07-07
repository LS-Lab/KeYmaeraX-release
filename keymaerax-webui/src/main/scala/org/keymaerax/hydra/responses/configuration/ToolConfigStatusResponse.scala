/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.configuration

import org.keymaerax.hydra.Response
import org.keymaerax.tools.ToolName
import spray.json.{JsBoolean, JsObject, JsString, JsValue}

import java.util.Locale

class ToolConfigStatusResponse(tool: ToolName.Value, configured: Boolean) extends Response {
  def getJson: JsValue = JsObject(
    // The webui expects this to be lowercase
    "tool" -> JsString(tool.toString.toLowerCase(Locale.ROOT)),
    "configured" -> JsBoolean(configured),
  )
}
