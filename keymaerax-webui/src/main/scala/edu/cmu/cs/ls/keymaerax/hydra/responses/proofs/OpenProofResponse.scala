/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.hydra.{ProofPOJO, Response}
import spray.json.{JsBoolean, JsNull, JsNumber, JsObject, JsString, JsValue}

case class OpenProofResponse(proof: ProofPOJO, loadStatus: String) extends Response {
  override val schema: Option[String] = Some("proof.js")
  def getJson: JsValue = JsObject(
    "id" -> JsString(proof.proofId.toString),
    "name" -> JsString(proof.name),
    "description" -> JsString(proof.description),
    "date" -> JsString(proof.date),
    "modelId" -> JsString(proof.modelId.toString),
    "stepCount" -> JsNumber(proof.stepCount),
    "status" -> JsBoolean(proof.closed),
    "tactic" -> (proof.tactic match { case None => JsNull case Some(t) => JsString(t) }),
    "loadStatus" -> JsString(loadStatus)
  )
}
