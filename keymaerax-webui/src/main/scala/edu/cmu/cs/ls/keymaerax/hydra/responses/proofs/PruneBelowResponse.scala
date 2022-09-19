/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.hydra.{AgendaItem, Helpers, Response}
import spray.json.JsObject

class PruneBelowResponse(item: AgendaItem) extends Response {
  def getJson: JsObject = JsObject(
    "agendaItem" -> Helpers.itemJson(item)._2
  )
}
