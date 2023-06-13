/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.btactics.AxIndex
import edu.cmu.cs.ls.keymaerax.btactics.macros.{AxiomDisplayInfo, ProvableInfo}
import edu.cmu.cs.ls.keymaerax.hydra.{RequestHelper, Response}
import spray.json.{JsArray, JsNull, JsObject, JsString, JsValue}

import scala.util.Try

case class LemmasResponse(infos: List[ProvableInfo]) extends Response {
  override def getJson: JsValue = {
    def getInfoJson(i: ProvableInfo): JsObject = {
      JsObject(
        "name" -> JsString(i.canonicalName),
        "codeName" -> JsString(i.codeName),
        "defaultKeyPos" -> {
          val key = AxIndex.axiomIndex(i)._1
          JsString(key.pos.mkString("."))
        },
        "displayInfo" -> (i.display match {
          case AxiomDisplayInfo(_, f) => JsString(f)
          case _ => JsNull
        }),
        "displayInfoParts" -> RequestHelper.jsonDisplayInfoComponents(i))
    }
    val json = infos.map(i => Try(getInfoJson(i)).toOption).filter(_.isDefined).map(_.get)
    JsObject("lemmas" -> JsArray(json:_*))
  }
}