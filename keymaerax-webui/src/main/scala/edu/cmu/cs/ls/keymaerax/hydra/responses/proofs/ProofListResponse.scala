/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.hydra.{ProofPOJO, Response}
import spray.json.{JsArray, JsBoolean, JsNumber, JsObject, JsString, JsValue}

/** @param proofs The list of proofs with their status in KeYmaera (proof, loadStatus). */
class ProofListResponse(proofs: List[(ProofPOJO, String)]) extends Response {
  override val schema: Option[String] = Some("prooflist.js")

  val objects: List[JsObject] = proofs.map({ case (proof, loadStatus) =>
    JsObject(
      "id" -> JsString(proof.proofId.toString),
      "name" -> JsString(proof.name),
      "description" -> JsString(proof.description),
      "date" -> JsString(proof.date),
      "modelId" -> JsString(proof.modelId.toString),
      "stepCount" -> JsNumber(proof.stepCount),
      "status" -> JsBoolean(proof.closed),
      "loadStatus" -> JsString(loadStatus),
    )
  })

  def getJson: JsValue = JsArray(objects: _*)
}
