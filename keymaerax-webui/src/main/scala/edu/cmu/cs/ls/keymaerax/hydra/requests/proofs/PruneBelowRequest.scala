/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.PruneBelowResponse
import edu.cmu.cs.ls.keymaerax.hydra.{
  AgendaItem,
  DBAbstraction,
  DbProofTree,
  ErrorResponse,
  Response,
  UserProofRequest,
  WriteRequest,
}

import scala.collection.immutable.{List, Nil}

/** Prunes a node and everything below */
class PruneBelowRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
    extends UserProofRequest(db, userId, proofId) with WriteRequest {
  override protected def doResultingResponses(): List[Response] = {
    if (db.getProofInfo(proofId).closed) new ErrorResponse("Pruning not allowed on closed proofs") :: Nil
    else {
      val tree = DbProofTree(db, proofId)
      tree.locate(nodeId) match {
        case None => new ErrorResponse("Unknown node " + nodeId) :: Nil
        case Some(node) =>
          node.pruneBelow()
          val item = AgendaItem(node.id.toString, AgendaItem.nameOf(node), proofId)
          new PruneBelowResponse(item) :: Nil
      }
    }
  }
}
