/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.{
  BellerophonTacticExecutor,
  DBAbstraction,
  GenericOKResponse,
  Response,
  UserProofRequest,
  WriteRequest,
}

class StopTaskRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, taskId: String)
    extends UserProofRequest(db, userId, proofId) with WriteRequest {
  override protected def doResultingResponse(): Response = {
    val executor = BellerophonTacticExecutor.defaultExecutor
    // @note may have completed in the meantime
    executor.tasksForUser(userId).foreach(executor.tryRemove(_, force = true))
    new GenericOKResponse()
  }
}
