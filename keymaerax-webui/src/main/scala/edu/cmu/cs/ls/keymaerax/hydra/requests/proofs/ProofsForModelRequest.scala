/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.ProofListResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ReadRequest, Response, UserRequest}

class ProofsForModelRequest(db: DBAbstraction, userId: String, modelId: String)
    extends UserRequest(userId, _ => true) with ReadRequest {
  def resultingResponse(): Response = {
    val proofs = db
      .getProofsForModel(modelId)
      .map(proof =>
        (proof, "loaded" /*KeYmaeraInterface.getTaskLoadStatus(proof.proofId.toString).toString.toLowerCase*/ )
      )
    new ProofListResponse(proofs)
  }
}
