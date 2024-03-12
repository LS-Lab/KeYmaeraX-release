/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.hydra.Helpers.{itemJson, nodesJson}
import edu.cmu.cs.ls.keymaerax.hydra.{AgendaItem, ProofTreeNode, Response}
import spray.json.{JsArray, JsObject, JsString, JsValue}

case class ExpandTacticResponse(
    detailsProofId: Int,
    goalSequents: List[Sequent],
    backendGoals: List[Option[(String, String)]],
    tacticParent: String,
    stepsTactic: String,
    tree: List[ProofTreeNode],
    openGoals: List[AgendaItem],
    marginLeft: Int,
    marginRight: Int,
) extends Response {
  private lazy val proofTree = {
    val theNodes: List[(String, JsValue)] = nodesJson(tree, marginLeft, marginRight, printAllSequents = true)
    JsObject("nodes" -> JsObject(theNodes.toMap), "root" -> JsString(tree.head.id.toString))
  }

  def getJson: JsValue = JsObject(
    "tactic" -> JsObject("stepsTactic" -> JsString(stepsTactic.trim()), "parent" -> JsString(tacticParent)),
    "detailsProofId" -> JsString(detailsProofId.toString),
    if (tree.nonEmpty) "proofTree" -> proofTree else "proofTree" -> JsObject(),
    "goalSequents" -> JsArray(goalSequents.map(g => JsString(g.toString)): _*),
    "backendGoals" -> JsArray(
      backendGoals.map(g =>
        if (g.nonEmpty) JsObject("mathematica" -> JsString(g.get._1), "z3" -> JsString(g.get._2)) else JsObject()
      ): _*
    ),
    "openGoals" -> JsObject(openGoals.map(itemJson): _*),
  )
}
