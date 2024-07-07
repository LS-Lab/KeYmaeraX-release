/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.proofs

import org.keymaerax.hydra.Helpers.sequentJson
import org.keymaerax.hydra.{ProofTreeNode, Response}
import spray.json.{JsNull, JsObject, JsString, JsValue}

case class ProofNodeSequentResponse(proofId: String, node: ProofTreeNode, marginLeft: Int, marginRight: Int)
    extends Response {
  def getJson: JsValue = JsObject(
    "proofId" -> JsString(proofId),
    "nodeId" -> JsString(node.id.toString),
    "sequent" ->
      (node.goal match {
        case None => JsNull
        case Some(goal) => sequentJson(goal, marginLeft, marginRight)
      }),
  )
}
