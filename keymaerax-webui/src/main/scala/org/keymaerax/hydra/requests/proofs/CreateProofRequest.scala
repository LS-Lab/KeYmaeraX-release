/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.{CreatedIdResponse, DBAbstraction, ErrorResponse, Response, UserRequest, WriteRequest}

class CreateProofRequest(db: DBAbstraction, userId: String, modelId: String, name: String, description: String)
    extends UserRequest(userId, _ => true) with WriteRequest {
  def resultingResponse(): Response = {
    if (modelId != "undefined") {
      val proofName = if (name.isEmpty) db.getModel(modelId).name + ": Proof" else name
      val proofId = db.createProofForModel(modelId, proofName, description, currentDate(), None)
      CreatedIdResponse(proofId)
    } else { new ErrorResponse("Unable to create proof for unknown model") }
  }
}
