/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.responses.models.GetModelTacticResponse
import org.keymaerax.hydra.{DBAbstraction, ReadRequest, Response, UserRequest}

class GetModelTacticRequest(db: DBAbstraction, userId: String, modelId: String)
    extends UserRequest(userId, _ => true) with ReadRequest {
  def resultingResponse(): Response = new GetModelTacticResponse(db.getModel(modelId))
}
