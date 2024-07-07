/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.configuration

import org.keymaerax.hydra.Response
import spray.json.{JsObject, JsString, JsValue}

class SystemInfoResponse(os: String, osVersion: String, jvmHome: String, jvmVendor: String, jvmVersion: String)
    extends Response {
  def getJson: JsValue = JsObject(
    "os" -> JsString(os),
    "osVersion" -> JsString(osVersion),
    "jvmHome" -> JsString(jvmHome),
    "jvmVendor" -> JsString(jvmVendor),
    "jvmVersion" -> JsString(jvmVersion),
  )
}
