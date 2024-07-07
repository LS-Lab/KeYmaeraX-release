/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.responses.proofs.ProofListResponse
import org.keymaerax.hydra.{DBAbstraction, ReadRequest, Response, UserRequest}

class ProofsForUserRequest(db: DBAbstraction, userId: String) extends UserRequest(userId, _ => true) with ReadRequest {
  def resultingResponse(): Response = {
    val proofs = db
      .getProofsForUser(userId)
      .filterNot(_._1.temporary)
      .map(proof =>
        (proof._1, "loaded" /*KeYmaeraInterface.getTaskLoadStatus(proof._1.proofId.toString).toString.toLowerCase*/ )
      )
    new ProofListResponse(proofs)
  }
}
