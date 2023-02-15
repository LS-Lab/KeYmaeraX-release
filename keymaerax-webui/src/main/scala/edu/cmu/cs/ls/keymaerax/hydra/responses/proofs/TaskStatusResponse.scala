/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleThrowable, BelleValue}
import edu.cmu.cs.ls.keymaerax.hydra.{ProofTreeNode, Response}
import spray.json.{JsArray, JsNull, JsNumber, JsObject, JsString, JsValue}

import scala.collection.immutable.Seq

case class TaskStatusResponse(proofId: String,
                              nodeId: String,
                              taskId: String,
                              status: String,
                              currentStep: Option[(BelleExpr, Long)],
                              progress: List[ProofTreeNode]) extends Response {
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
        "stepStatus" -> JsNull
      ),
      "progress" -> JsArray(progress.map(e =>
        JsObject(
          "maker" -> JsString(e.maker.getOrElse("<unknown>"))
        )
      ):_*)
    )
  }

}
