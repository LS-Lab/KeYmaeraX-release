/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.responses.configuration

import edu.cmu.cs.ls.keymaerax.hydra.Response
import spray.json.{JsObject, JsString, JsValue}

class FullConfigurationResponse(content: String) extends Response {
  override def getJson: JsValue = JsObject(
    "content" -> JsString(content)
  )
}
