/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.users

import edu.cmu.cs.ls.keymaerax.hydra.Response
import spray.json.{JsBoolean, JsObject, JsString}

case class DefaultLoginResponse(triggerRegistration: Boolean) extends Response {
  override def getJson: JsObject =
    JsObject(Map("type" -> JsString("LoginResponse"), "triggerRegistration" -> JsBoolean(triggerRegistration)))
}
