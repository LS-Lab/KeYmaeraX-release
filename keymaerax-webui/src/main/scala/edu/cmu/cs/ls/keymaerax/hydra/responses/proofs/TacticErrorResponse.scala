/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleThrowable, BelleUnexpectedProofStateError, CompoundCriticalException}
import edu.cmu.cs.ls.keymaerax.hydra.ErrorResponse
import spray.json.{JsObject, JsString, JsValue}

class TacticErrorResponse(msg: String, tacticMsg: String, exn: Throwable = null)
  extends ErrorResponse(msg, exn, severity = "tacticerror") {
  override def getJson: JsValue = exn match {
    case _: BelleUnexpectedProofStateError =>
      JsObject(super.getJson.asJsObject.fields ++ Map(
        "tacticMsg" -> JsString(tacticMsg)
      ))
    case ex: CompoundCriticalException =>
      val exceptions = flatten(ex)
      val messages = exceptions.zipWithIndex.map({
        case (x: BelleUnexpectedProofStateError, i) =>
          s"${i + 1}. ${x.getMessage}:\n${x.proofState.subgoals.map(_.toString).mkString(",")}"
        case (x, i) => s"${i + 1}. ${x.getMessage}"
      })
      val message = s"${exceptions.size} tactic attempts failed:\n${messages.mkString("\n")}\n"
      JsObject(super.getJson.asJsObject.fields.filter(_._1 != "textStatus") ++ Map(
        "textStatus" -> JsString(message),
        "tacticMsg" -> JsString(tacticMsg)
      ))
    case _ =>
      JsObject(super.getJson.asJsObject.fields ++ Map(
        "tacticMsg" -> JsString(tacticMsg)
      ))
  }

  private def flatten(ex: BelleThrowable): List[BelleThrowable] = ex match {
    case ex: CompoundCriticalException => flatten(ex.left) ++ flatten(ex.right)
    case _ => ex :: Nil
  }
}
