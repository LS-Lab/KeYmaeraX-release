/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.configuration

import edu.cmu.cs.ls.keymaerax.hydra.Response
import edu.cmu.cs.ls.keymaerax.tools.ToolName
import spray.json.{JsBoolean, JsObject, JsString, JsValue}

import java.util.Locale

class ToolConfigStatusResponse(tool: ToolName.Value, configured: Boolean) extends Response {
  def getJson: JsValue = JsObject(
    // The webui expects this to be lowercase
    "tool" -> JsString(tool.toString.toLowerCase(Locale.ROOT)),
    "configured" -> JsBoolean(configured),
  )
}
