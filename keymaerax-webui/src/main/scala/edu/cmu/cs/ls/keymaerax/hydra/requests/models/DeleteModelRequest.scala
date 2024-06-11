/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.models

import edu.cmu.cs.ls.keymaerax.hydra.{BooleanResponse, DBAbstraction, Response, UserModelRequest, WriteRequest}

class DeleteModelRequest(db: DBAbstraction, userId: String, modelId: String)
    extends UserModelRequest(db, userId, modelId) with WriteRequest {
  override def doResultingResponse(): Response = {
    val id = Integer.parseInt(modelId)
    // db.getProofsForModel(id).foreach(proof => TaskManagement.forceDeleteTask(proof.proofId.toString))
    val success = db.deleteModel(id)
    BooleanResponse(success)
  }
}
