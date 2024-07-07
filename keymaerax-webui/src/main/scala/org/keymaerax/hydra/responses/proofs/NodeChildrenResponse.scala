/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.proofs

import org.keymaerax.hydra.Helpers.nodesJson
import org.keymaerax.hydra.{ProofTreeNode, Response}
import spray.json.{JsArray, JsBoolean, JsObject, JsString, JsValue}

case class NodeChildrenResponse(proofId: String, parent: ProofTreeNode, marginLeft: Int, marginRight: Int)
    extends Response {
  def getJson: JsValue = JsObject(
    "proofId" -> JsString(proofId),
    "parent" -> JsObject(
      "id" -> JsString(parent.id.toString),
      "children" -> JsArray(parent.children.map(c => JsString(c.id.toString)): _*),
    ),
    "newNodes" -> JsArray(nodesJson(parent.children, marginLeft, marginRight).map(_._2): _*),
    "progress" -> JsBoolean(true),
  )
}
