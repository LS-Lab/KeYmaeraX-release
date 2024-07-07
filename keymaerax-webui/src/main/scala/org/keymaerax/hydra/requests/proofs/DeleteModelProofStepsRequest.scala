/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.{BooleanResponse, DBAbstraction, Response, UserModelRequest, WriteRequest}

class DeleteModelProofStepsRequest(db: DBAbstraction, userId: String, modelId: String)
    extends UserModelRequest(db, userId, modelId) with WriteRequest {
  override def doResultingResponse(): Response = {
    val modelProofs = db.getProofsForModel(modelId)
    val deleted = modelProofs.map(p => (p.stepCount, db.deleteProofSteps(p.proofId)))
    BooleanResponse(deleted.forall({ case (hadSteps, deletedSteps) => hadSteps == deletedSteps }))
  }
}
