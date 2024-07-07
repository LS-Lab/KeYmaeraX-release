/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.proofs

import org.keymaerax.hydra.{AgendaItem, Helpers, Response}
import spray.json.JsObject

class PruneBelowResponse(item: AgendaItem) extends Response {
  def getJson: JsObject = JsObject("agendaItem" -> Helpers.itemJson(item)._2)
}
