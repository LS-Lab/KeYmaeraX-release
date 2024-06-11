/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.{BooleanResponse, DBAbstraction, Response, UserRequest, WriteRequest}

class AddModelTacticRequest(db: DBAbstraction, userId: String, modelId: String, tactic: String)
    extends UserRequest(userId, _ => true) with WriteRequest {
  def resultingResponse(): Response = {
    val tacticId = db.addModelTactic(modelId, tactic)
    BooleanResponse(tacticId.isDefined)
  }
}
