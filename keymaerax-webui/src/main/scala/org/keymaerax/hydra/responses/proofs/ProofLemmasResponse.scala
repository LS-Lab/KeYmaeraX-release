/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.proofs

import org.keymaerax.hydra.Response
import spray.json.{JsArray, JsNumber, JsObject, JsString, JsValue}

case class ProofLemmasResponse(lemmas: List[(String, Int)]) extends Response {
  def getJson: JsValue = JsObject({
    "lemmas" -> JsArray(lemmas.map(l => JsObject("name" -> JsString(l._1), "proofId" -> JsNumber(l._2))): _*)
  })
}
