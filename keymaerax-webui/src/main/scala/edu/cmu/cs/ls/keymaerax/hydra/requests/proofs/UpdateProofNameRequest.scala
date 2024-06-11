/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.UpdateProofNameResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, Response, UserProofRequest, WriteRequest}

class UpdateProofNameRequest(db: DBAbstraction, userId: String, proofId: String, newName: String)
    extends UserProofRequest(db, userId, proofId) with WriteRequest {
  override protected def doResultingResponse(): Response = {
    db.updateProofName(proofId, newName)
    new UpdateProofNameResponse(proofId, newName)
  }
}
