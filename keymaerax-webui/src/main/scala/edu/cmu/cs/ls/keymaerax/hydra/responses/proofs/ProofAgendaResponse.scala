/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.hydra.{Helpers, ProofPOJO, Response}
import spray.json.{JsArray, JsObject, JsString, JsValue, JsonParser}

class ProofAgendaResponse(tasks: List[(ProofPOJO, List[Int], String)]) extends Response {
  override val schema: Option[String] = Some("proofagenda.js")
  val objects: List[JsObject] = tasks.map({ case (proofPojo, nodeId, nodeJson) => JsObject(
    "proofId" -> JsString(proofPojo.proofId.toString),
    "nodeId" -> Helpers.nodeIdJson(nodeId),
    "proofNode" -> JsonParser(nodeJson)
  )})

  def getJson: JsValue = JsArray(objects:_*)
}
