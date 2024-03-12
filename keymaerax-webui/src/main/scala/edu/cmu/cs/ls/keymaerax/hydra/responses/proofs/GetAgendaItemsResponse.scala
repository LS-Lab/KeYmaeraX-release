/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.hydra.Helpers.agendaItemJson
import edu.cmu.cs.ls.keymaerax.hydra.{AgendaItemPOJO, Response}
import spray.json.JsValue

class GetAgendaItemResponse(item: AgendaItemPOJO) extends Response {
  def getJson: JsValue = agendaItemJson(item)
}
