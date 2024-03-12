/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.tools

import edu.cmu.cs.ls.keymaerax.hydra.Response
import spray.json.{JsBoolean, JsNumber, JsObject, JsString, JsValue}

class ToolStatusResponse(tool: String, availableWorkers: Int) extends Response {
  def getJson: JsValue = JsObject(
    "tool" -> JsString(tool),
    "busy" -> JsBoolean(availableWorkers <= 0),
    "availableWorkers" -> JsNumber(availableWorkers),
  )
}
