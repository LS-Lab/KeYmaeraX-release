/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.hydra.Response
import spray.json.{JsBoolean, JsObject, JsString}

class ValidateProofResponse(taskId: String, proved: Option[Boolean]) extends Response {
  def getJson: JsObject = proved match {
    case Some(isProved) =>
      JsObject("uuid" -> JsString(taskId), "running" -> JsBoolean(false), "proved" -> JsBoolean(isProved))
    case None => JsObject("uuid" -> JsString(taskId), "running" -> JsBoolean(true))
  }
}
