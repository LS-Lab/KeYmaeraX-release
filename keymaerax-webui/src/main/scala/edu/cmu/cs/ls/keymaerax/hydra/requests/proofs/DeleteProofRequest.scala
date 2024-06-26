/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.{BooleanResponse, DBAbstraction, Response, UserProofRequest, WriteRequest}

class DeleteProofRequest(db: DBAbstraction, userId: String, proofId: String)
    extends UserProofRequest(db, userId, proofId) with WriteRequest {
  override protected def doResultingResponse(): Response = {
    // TaskManagement.forceDeleteTask(proofId)
    val success = db.deleteProof(Integer.parseInt(proofId))
    BooleanResponse(success)
  }
}
