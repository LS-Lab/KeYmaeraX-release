/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.proofs

import org.keymaerax.hydra.Response
import org.keymaerax.parser.{Location, Region}
import spray.json.{JsArray, JsNumber, JsObject, JsString, JsValue}

case class GetTacticResponse(tacticText: String, nodesByLoc: Map[Location, String]) extends Response {
  private def locJson(l: Location) = l match {
    case Region(l, c, el, ec) =>
      JsObject("line" -> JsNumber(l), "column" -> JsNumber(c), "endLine" -> JsNumber(el), "endColumn" -> JsNumber(ec))
    case _ => throw new IllegalArgumentException("Unknown location kind " + l.getClass)
  }
  private def nodeByLoc(l: Location, n: String) = JsObject("loc" -> locJson(l), "node" -> JsString(n))
  def getJson: JsValue = JsObject(
    "tacticText" -> JsString(tacticText),
    "nodesByLocation" -> JsArray(nodesByLoc.map({ case (k, v) => nodeByLoc(k, v) }).toVector),
  )
}
