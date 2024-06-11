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

class CreateModelTacticProofRequest(db: DBAbstraction, userId: String, modelId: String)
    extends UserRequest(userId, _ => true) with WriteRequest {
  def resultingResponse(): Response = {
    val model = db.getModel(modelId)
    model.tactic match {
      case Some(tacticText) =>
        val proofId = db.createProofForModel(
          Integer.parseInt(modelId),
          model.name + " from tactic",
          "Proof from tactic",
          currentDate(),
          Some(tacticText),
        )
        CreatedIdResponse(proofId.toString)
      case None => new ErrorResponse("Model " + modelId + " does not have a tactic associated")
    }
  }
}
