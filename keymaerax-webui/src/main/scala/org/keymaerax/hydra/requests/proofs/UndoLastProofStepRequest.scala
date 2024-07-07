/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.responses.proofs.PruneBelowResponse
import org.keymaerax.hydra.{
  AgendaItem,
  DBAbstraction,
  DbProofTree,
  ErrorResponse,
  Response,
  UserProofRequest,
  WriteRequest,
}

/** Undoes the last proof step. */
class UndoLastProofStepRequest(db: DBAbstraction, userId: String, proofId: String)
    extends UserProofRequest(db, userId, proofId) with WriteRequest {
  override protected def doResultingResponse(): Response = {
    val tree = DbProofTree(db, proofId)
    // @todo do not load all steps
    tree.nodes.lastOption.flatMap(_.parent) match {
      case None => new ErrorResponse("Proof does not have any steps yet")
      case Some(node) =>
        node.pruneBelow()
        val info = db.getProofInfo(proofId)
        db.updateProofInfo(info.copy(closed = false))
        val item = AgendaItem(node.id.toString, AgendaItem.nameOf(node), proofId, node.allAncestors.map(_.id.toString))
        new PruneBelowResponse(item)
    }
  }
}
