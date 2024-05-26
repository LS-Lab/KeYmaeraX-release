/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.configuration

import edu.cmu.cs.ls.keymaerax.hydra.Response
import edu.cmu.cs.ls.keymaerax.info.ArchType
import spray.json.{JsObject, JsString, JsValue}

class SystemInfoResponse(
    os: String,
    osVersion: String,
    jvmHome: String,
    jvmVendor: String,
    jvmVersion: String,
    jvmBits: ArchType,
) extends Response {
  def getJson: JsValue = JsObject(
    "os" -> JsString(os),
    "osVersion" -> JsString(osVersion),
    "jvmHome" -> JsString(jvmHome),
    "jvmVendor" -> JsString(jvmVendor),
    "jvmVersion" -> JsString(jvmVersion),
    "jvmArchitecture" -> JsString(jvmBits match {
      case ArchType.Bit32 => "32"
      case ArchType.Bit64 => "64"
      case ArchType.Unknown => "unknown"
    }),
  )
}
