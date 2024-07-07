/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.responses.proofs

import org.keymaerax.hydra.Response
import org.keymaerax.pt.ProvableSig
import spray.json.{JsBoolean, JsObject, JsString, JsValue}

class ProofVerificationResponse(proofId: String, provable: ProvableSig, tactic: String) extends Response {
  override def getJson: JsValue = JsObject(
    "proofId" -> JsString(proofId),
    "isProved" -> JsBoolean(provable.isProved),
    "provable" -> JsString(provable.underlyingProvable.toString),
    "tactic" -> JsString(tactic),
  )
}
