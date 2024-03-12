/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.hydra.Response
import spray.json.{JsObject, JsString, JsValue, JsonParser}

class ProofTreeResponse(tree: String) extends Response {
  def getJson: JsValue = JsObject("type" -> JsString("proof"), "tree" -> JsonParser(tree))
}
