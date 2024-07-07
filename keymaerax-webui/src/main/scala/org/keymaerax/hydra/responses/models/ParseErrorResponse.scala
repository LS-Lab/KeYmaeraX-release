/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.models

import org.keymaerax.hydra.ErrorResponse
import org.keymaerax.parser.Location
import spray.json.{JsNumber, JsObject, JsString, JsValue}

case class ParseErrorResponse(
    override val msg: String,
    expect: String,
    found: String,
    detailedMsg: String,
    loc: Location,
    override val exn: Throwable = null,
) extends ErrorResponse(msg, exn) {
  override def getJson: JsValue = JsObject(
    super.getJson.asJsObject.fields ++ Map(
      "details" ->
        JsObject("expect" -> JsString(expect), "found" -> JsString(found), "detailedMsg" -> JsString(detailedMsg)),
      "location" -> JsObject("line" -> JsNumber(loc.line), "column" -> JsNumber(loc.column)),
    )
  )
}
