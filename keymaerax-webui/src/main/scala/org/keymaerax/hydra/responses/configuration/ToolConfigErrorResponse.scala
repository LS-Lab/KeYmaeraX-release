/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.configuration

import org.keymaerax.hydra.ErrorResponse
import org.keymaerax.tools.ToolName
import spray.json.{JsObject, JsString}

import java.util.Locale

class ToolConfigErrorResponse(tool: ToolName.Value, msg: String) extends ErrorResponse(msg, null) {
  override def getJson: JsObject = JsObject(
    super.getJson.asJsObject.fields ++ Map(
      // The webui expects this to be lowercase
      "tool" -> JsString(tool.toString.toLowerCase(Locale.ROOT))
    )
  )
}
