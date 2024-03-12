/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.hydra.Helpers.nodesJson
import edu.cmu.cs.ls.keymaerax.hydra.{ProofTreeNode, Response}
import spray.json.{JsArray, JsBoolean, JsObject, JsString, JsValue}

case class TaskResultResponse(
    proofId: String,
    parent: ProofTreeNode,
    marginLeft: Int,
    marginRight: Int,
    progress: Boolean = true,
) extends Response {
  private lazy val openChildren = parent.children.filter(_.numSubgoals > 0)

  def getJson: JsValue = JsObject(
    "proofId" -> JsString(proofId),
    "parent" -> JsObject(
      "id" -> JsString(parent.id.toString),
      "children" -> JsArray(openChildren.map(c => JsString(c.id.toString)): _*),
    ),
    "newNodes" -> JsArray(nodesJson(openChildren, marginLeft, marginRight).map(_._2): _*),
    "progress" -> JsBoolean(progress),
    "type" -> JsString("taskresult"),
  )
}
