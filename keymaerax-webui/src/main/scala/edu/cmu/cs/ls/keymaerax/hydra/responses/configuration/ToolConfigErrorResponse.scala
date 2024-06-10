/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.configuration

import edu.cmu.cs.ls.keymaerax.hydra.ErrorResponse
import edu.cmu.cs.ls.keymaerax.tools.ToolName
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
