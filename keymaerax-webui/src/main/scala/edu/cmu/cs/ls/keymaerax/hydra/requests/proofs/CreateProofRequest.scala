/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.{
  CreatedIdResponse,
  DBAbstraction,
  ErrorResponse,
  Response,
  UserRequest,
  WriteRequest,
}

import scala.collection.immutable.{List, Nil}

class CreateProofRequest(db: DBAbstraction, userId: String, modelId: String, name: String, description: String)
    extends UserRequest(userId, _ => true) with WriteRequest {
  def resultingResponses(): List[Response] = {
    if (modelId != "undefined") {
      val proofName = if (name.isEmpty) db.getModel(modelId).name + ": Proof" else name
      val proofId = db.createProofForModel(modelId, proofName, description, currentDate(), None)
      CreatedIdResponse(proofId) :: Nil
    } else { new ErrorResponse("Unable to create proof for unknown model") :: Nil }
  }
}
