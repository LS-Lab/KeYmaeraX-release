/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.hydra.{ProofTreeNode, Response}
import spray.json.{JsArray, JsNull, JsNumber, JsObject, JsString, JsValue}

import scala.collection.immutable.List

case class TaskStatusResponse(
    proofId: String,
    nodeId: String,
    taskId: String,
    status: String,
    currentStep: Option[(BelleExpr, Long)],
    stepsProgress: List[ProofTreeNode],
    tacticProgress: String,
) extends Response {
  def getJson: JsValue = {
    JsObject(
      "proofId" -> JsString(proofId),
      "parentId" -> JsString(nodeId),
      "taskId" -> JsString(taskId),
      "status" -> JsString(status),
      "type" -> JsString("taskstatus"),
      "currentStep" -> JsObject(
        "ruleName" -> currentStep.map(c => JsString(c._1.prettyString)).getOrElse(JsNull),
        "duration" -> currentStep.map(c => JsNumber(c._2)).getOrElse(JsNull),
        "stepStatus" -> JsNull,
      ),
      "progress" -> JsObject(
        "steps" -> JsArray(
          stepsProgress.map(e =>
            JsObject("id" -> JsString(e.id.toString), "maker" -> JsString(e.maker.getOrElse("<unknown>")))
          ): _*
        ),
        "tactic" -> JsString(tacticProgress),
      ),
    )
  }

}
