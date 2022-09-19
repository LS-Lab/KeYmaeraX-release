/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.responses.configuration

import edu.cmu.cs.ls.keymaerax.hydra.ErrorResponse
import spray.json.{JsObject, JsString}

class ToolConfigErrorResponse(tool: String, msg: String) extends ErrorResponse(msg, null) {
  override def getJson: JsObject = JsObject(super.getJson.asJsObject.fields ++ Map("tool" -> JsString(tool)))
}
