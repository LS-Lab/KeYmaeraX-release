/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.configuration

import org.keymaerax.hydra.Response
import spray.json.{JsFalse, JsObject, JsString, JsTrue, JsValue}

class ConfigureMathematicaResponse(linkNamePrefix: String, jlinkLibDirPrefix: String, success: Boolean)
    extends Response {
  def getJson: JsValue = JsObject(
    "linkNamePrefix" -> JsString(linkNamePrefix),
    "jlinkLibDirPrefix" -> JsString(jlinkLibDirPrefix),
    "success" -> { if (success) JsTrue else JsFalse },
  )
}
