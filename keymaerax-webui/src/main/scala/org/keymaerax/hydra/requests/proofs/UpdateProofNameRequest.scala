/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.responses.proofs.UpdateProofNameResponse
import org.keymaerax.hydra.{DBAbstraction, Response, UserProofRequest, WriteRequest}

class UpdateProofNameRequest(db: DBAbstraction, userId: String, proofId: String, newName: String)
    extends UserProofRequest(db, userId, proofId) with WriteRequest {
  override protected def doResultingResponse(): Response = {
    db.updateProofName(proofId, newName)
    new UpdateProofNameResponse(proofId, newName)
  }
}
