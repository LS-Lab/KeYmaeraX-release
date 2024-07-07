/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.configuration

import org.keymaerax.hydra.Response
import spray.json.{JsBoolean, JsObject, JsString}

class KeymaeraXVersionResponse(installedVersion: String, upToDate: Option[Boolean], latestVersion: Option[String])
    extends Response {
  assert(
    upToDate.isDefined == latestVersion.isDefined,
    "upToDate and latestVersion should both be defined, or both be undefined.",
  )
  def getJson: JsObject = upToDate match {
    case Some(b) => JsObject(
        "keymaeraXVersion" -> JsString(installedVersion),
        "upToDate" -> JsBoolean(b),
        "latestVersion" -> JsString(latestVersion.get),
      )
    case None => JsObject("keymaeraXVersion" -> JsString(installedVersion))
  }
}
