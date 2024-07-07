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

/** Prunes a node and everything below */
class PruneBelowRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
    extends UserProofRequest(db, userId, proofId) with WriteRequest {
  override protected def doResultingResponse(): Response = {
    if (db.getProofInfo(proofId).closed) new ErrorResponse("Pruning not allowed on closed proofs")
    else {
      val tree = DbProofTree(db, proofId)
      tree.locate(nodeId) match {
        case None => new ErrorResponse("Unknown node " + nodeId)
        case Some(node) =>
          node.pruneBelow()
          val item = AgendaItem(node.id.toString, AgendaItem.nameOf(node), proofId)
          new PruneBelowResponse(item)
      }
    }
  }
}
