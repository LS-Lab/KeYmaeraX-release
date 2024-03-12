/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.users

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.hydra.{Response, UserPOJO}
import spray.json.{JsFalse, JsNumber, JsObject, JsString, JsTrue, JsValue}

class LoginResponse(flag: Boolean, user: UserPOJO, sessionToken: Option[String]) extends Response {
  def getJson: JsValue = JsObject(
    "success" -> (if (flag) JsTrue else JsFalse),
    "sessionToken" -> (if (flag && sessionToken.isDefined) JsString(sessionToken.get) else JsFalse),
    "key" -> JsString("userId"),
    "value" -> JsString(user.userName.replace("/", "%2F").replace(":", "%3A")),
    "userAuthLevel" -> JsNumber(user.level),
    "askUseDefaultUser" ->
      (if (Configuration.getString(Configuration.Keys.USE_DEFAULT_USER).contains("false")) JsFalse else JsTrue),
    "type" -> JsString("LoginResponse"),
  )
}
