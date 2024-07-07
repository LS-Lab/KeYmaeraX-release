/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.models

import org.keymaerax.hydra.{BooleanResponse, DBAbstraction, Response, UserRequest, WriteRequest}

class DeleteAllModelsRequest(db: DBAbstraction, userId: String)
    extends UserRequest(userId, _ => true) with WriteRequest {
  override def resultingResponse(): Response = {
    val allModels = db.getModelList(userId).map(_.modelId)
    allModels.foreach(db.deleteModel)
    BooleanResponse(flag = true)
  }
}
