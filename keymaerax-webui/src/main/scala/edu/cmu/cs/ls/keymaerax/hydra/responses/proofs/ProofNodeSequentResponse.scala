/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.hydra.Helpers.sequentJson
import edu.cmu.cs.ls.keymaerax.hydra.{ProofTreeNode, Response}
import spray.json.{JsNull, JsObject, JsString, JsValue}

case class ProofNodeSequentResponse(proofId: String, node: ProofTreeNode, marginLeft: Int, marginRight: Int) extends Response {
  def getJson: JsValue = JsObject(
    "proofId" -> JsString(proofId),
    "nodeId" -> JsString(node.id.toString),
    "sequent" -> (node.goal match { case None => JsNull case Some(goal) => sequentJson(goal, marginLeft, marginRight) })
  )
}
