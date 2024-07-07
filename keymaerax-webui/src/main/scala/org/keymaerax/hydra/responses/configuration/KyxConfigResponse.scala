/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.configuration

import org.keymaerax.hydra.Response
import spray.json.{JsObject, JsString, JsValue}

class KyxConfigResponse(kyxConfig: String) extends Response {
  def getJson: JsValue = JsObject("kyxConfig" -> JsString(kyxConfig))
}
