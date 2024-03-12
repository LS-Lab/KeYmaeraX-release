/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.responses.proofs

import edu.cmu.cs.ls.keymaerax.hydra.Response
import spray.json.{JsArray, JsValue}

class UpdateProofNameResponse(proofId: String, newName: String) extends Response {
  def getJson: JsValue = JsArray()
}
