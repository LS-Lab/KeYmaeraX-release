/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.responses.models

import edu.cmu.cs.ls.keymaerax.hydra.{Response, TemplatePOJO}
import spray.json.{JsArray, JsNull, JsNumber, JsObject, JsString, JsValue}

class GetTemplatesResponse(templates: List[TemplatePOJO]) extends Response {
  def getJson: JsValue = JsArray(
    templates.map(t =>
      JsObject(
        "title" -> JsString(t.title),
        "description" -> JsString(t.description),
        "text" -> JsString(t.text),
        "selectRange" -> t.selectRange.map(r => JsObject(
          "start" -> JsObject("row" -> JsNumber(r.line), "column" -> JsNumber(r.column)),
          "end" -> JsObject("row" -> JsNumber(r.endLine), "column" -> JsNumber(r.endColumn))
        )).getOrElse(JsNull),
        "imageUrl" -> t.imageUrl.map(JsString(_)).getOrElse(JsNull)
      )
    ).toVector
  )
}
