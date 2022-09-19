/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleThrowable, BelleValue}
import edu.cmu.cs.ls.keymaerax.hydra.Response
import spray.json.{JsArray, JsNull, JsNumber, JsObject, JsString, JsValue}

import scala.collection.immutable.Seq

case class TaskStatusResponse(proofId: String, nodeId: String, taskId: String, status: String,
                              progress: Option[(Option[(BelleExpr, Long)], Seq[(BelleExpr, Either[BelleValue, BelleThrowable])])]) extends Response {
  def getJson: JsValue = {
    JsObject(
      "proofId" -> JsString(proofId),
      "parentId" -> JsString(nodeId),
      "taskId" -> JsString(taskId),
      "status" -> JsString(status),
      "type" -> JsString("taskstatus"),
      "currentStep" -> progress.map(p => JsObject(
        "ruleName" -> p._1.map(c => JsString(c._1.prettyString)).getOrElse(JsNull),
        "duration" -> p._1.map(c => JsNumber(c._2)).getOrElse(JsNull),
        "stepStatus" -> JsNull
      )).getOrElse(JsNull),
      "progress" -> progress.map(p => JsArray(
        p._2.map(e => JsString(e._1.prettyString)):_*
      )).getOrElse(JsArray())
    )
  }

}
