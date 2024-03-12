/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.{
  BellerophonTacticExecutor,
  DBAbstraction,
  GenericOKResponse,
  Response,
  UserProofRequest,
  WriteRequest,
}

import scala.collection.immutable.{List, Nil}

class StopTaskRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, taskId: String)
    extends UserProofRequest(db, userId, proofId) with WriteRequest {
  override protected def doResultingResponses(): List[Response] = {
    val executor = BellerophonTacticExecutor.defaultExecutor
    // @note may have completed in the meantime
    executor.tasksForUser(userId).foreach(executor.tryRemove(_, force = true))
    new GenericOKResponse() :: Nil
  }
}
