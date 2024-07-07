/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.proofs

import org.keymaerax.hydra.Helpers.{itemJson, nodeJson, nodesJson, proofIdJson}
import org.keymaerax.hydra.{AgendaItem, ProofTreeNode, Response}
import spray.json.{JsBoolean, JsObject, JsString, JsValue}

case class AgendaAwesomeResponse(
    modelId: String,
    proofId: String,
    root: ProofTreeNode,
    leaves: List[ProofTreeNode],
    agenda: List[AgendaItem],
    closed: Boolean,
    marginLeft: Int,
    marginRight: Int,
) extends Response {
  override val schema: Option[String] = Some("agendaawesome.js")

  private lazy val proofTree = {
    val theNodes: List[(String, JsValue)] = nodeJson(root, withSequent = false, marginLeft, marginRight) +:
      nodesJson(leaves, marginLeft, marginRight)
    JsObject(
      "id" -> proofIdJson(proofId),
      "nodes" -> JsObject(theNodes.toMap),
      "root" -> JsString(root.id.toString),
      "isProved" -> JsBoolean(root.isProved),
    )
  }

  private lazy val agendaItems = JsObject(agenda.map(itemJson): _*)

  def getJson: JsValue = JsObject(
    "modelId" -> JsString(modelId),
    "proofTree" -> proofTree,
    "agendaItems" -> agendaItems,
    "closed" -> JsBoolean(closed),
  )
}
