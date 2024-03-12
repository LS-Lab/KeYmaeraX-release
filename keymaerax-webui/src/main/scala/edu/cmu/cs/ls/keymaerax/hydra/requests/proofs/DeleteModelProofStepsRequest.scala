/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.{BooleanResponse, DBAbstraction, Response, UserModelRequest, WriteRequest}

import scala.collection.immutable.{List, Nil}

class DeleteModelProofStepsRequest(db: DBAbstraction, userId: String, modelId: String)
    extends UserModelRequest(db, userId, modelId) with WriteRequest {
  override def doResultingResponses(): List[Response] = {
    val modelProofs = db.getProofsForModel(modelId)
    val deleted = modelProofs.map(p => (p.stepCount, db.deleteProofSteps(p.proofId)))
    BooleanResponse(deleted.forall({ case (hadSteps, deletedSteps) => hadSteps == deletedSteps })) :: Nil
  }
}
