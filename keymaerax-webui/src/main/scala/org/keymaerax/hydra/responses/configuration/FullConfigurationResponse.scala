/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.configuration

import org.keymaerax.hydra.Response
import spray.json.{JsObject, JsString, JsValue}

class FullConfigurationResponse(content: String) extends Response {
  override def getJson: JsValue = JsObject("content" -> JsString(content))
}
