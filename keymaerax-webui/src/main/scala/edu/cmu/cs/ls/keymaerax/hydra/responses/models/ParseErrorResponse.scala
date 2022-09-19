/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.responses.models

import edu.cmu.cs.ls.keymaerax.hydra.ErrorResponse
import edu.cmu.cs.ls.keymaerax.parser.Location
import spray.json.{JsNumber, JsObject, JsString, JsValue}

case class ParseErrorResponse(override val msg: String, expect: String, found: String, detailedMsg: String,
                              loc: Location, override val exn: Throwable = null) extends ErrorResponse(msg, exn) {
  override def getJson: JsValue = JsObject(super.getJson.asJsObject.fields ++ Map(
    "details" -> JsObject(
      "expect" -> JsString(expect),
      "found" -> JsString(found),
      "detailedMsg" -> JsString(detailedMsg)
    ),
    "location" -> JsObject(
      "line" -> JsNumber(loc.line),
      "column" -> JsNumber(loc.column)
    )
  ))
}