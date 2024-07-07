/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.tools

import org.keymaerax.core.Formula
import org.keymaerax.hydra.Response
import spray.json.{JsArray, JsBoolean, JsObject, JsString, JsValue}

import scala.collection.immutable.Seq

class PegasusCandidatesResponse(candidates: Seq[Either[Seq[(Formula, String)], Seq[(Formula, String)]]])
    extends Response {
  // @todo formula JSON with HTML formatting in UI
  override def getJson: JsValue = JsObject(
    "candidates" -> JsArray(
      candidates
        .map({
          case Left(invs) => JsObject(
              "fmls" -> JsArray(
                invs.map(f => JsObject("text" -> JsString(f._1.prettyString), "method" -> JsString(f._2))).toVector
              ),
              "isInv" -> JsBoolean(true),
            )
          case Right(invs) => JsObject(
              "fmls" -> JsArray(
                invs.map(f => JsObject("text" -> JsString(f._1.prettyString), "method" -> JsString(f._2))).toVector
              ),
              "isInv" -> JsBoolean(false),
            )
        })
        .toVector
    )
  )
}
