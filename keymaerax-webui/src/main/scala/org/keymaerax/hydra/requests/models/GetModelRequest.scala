/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.models

import org.keymaerax.hydra.responses.models.GetModelResponse
import org.keymaerax.hydra.{DBAbstraction, ReadRequest, Response, UserRequest}

class GetModelRequest(db: DBAbstraction, userId: String, modelId: String)
    extends UserRequest(userId, (id: String) => db.getModel(modelId).userId == id) with ReadRequest {
  def resultingResponse(): Response = new GetModelResponse(db.getModel(modelId))
}
