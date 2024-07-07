/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.responses.proofs.ProofProgressResponse
import org.keymaerax.hydra.{DBAbstraction, ReadRequest, Response, UserProofRequest}

class GetProofProgressStatusRequest(db: DBAbstraction, userId: String, proofId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    // @todo return Loading/NotLoaded when appropriate
    val proof = db.getProofInfo(proofId)
    new ProofProgressResponse(proofId, isClosed = proof.closed)
  }
}
