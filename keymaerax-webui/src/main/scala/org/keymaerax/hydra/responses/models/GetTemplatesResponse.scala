/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.models

import org.keymaerax.hydra.{Response, TemplatePOJO}
import spray.json.{JsArray, JsNull, JsNumber, JsObject, JsString, JsValue}

class GetTemplatesResponse(templates: List[TemplatePOJO]) extends Response {
  def getJson: JsValue = JsArray(
    templates
      .map(t =>
        JsObject(
          "title" -> JsString(t.title),
          "description" -> JsString(t.description),
          "text" -> JsString(t.text),
          "selectRange" ->
            t.selectRange
              .map(r =>
                JsObject(
                  "start" -> JsObject("row" -> JsNumber(r.line), "column" -> JsNumber(r.column)),
                  "end" -> JsObject("row" -> JsNumber(r.endLine), "column" -> JsNumber(r.endColumn)),
                )
              )
              .getOrElse(JsNull),
          "imageUrl" -> t.imageUrl.map(JsString(_)).getOrElse(JsNull),
        )
      )
      .toVector
  )
}
