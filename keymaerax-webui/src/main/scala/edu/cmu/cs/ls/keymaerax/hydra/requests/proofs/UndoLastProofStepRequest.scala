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

/** Undoes the last proof step. */
class UndoLastProofStepRequest(db: DBAbstraction, userId: String, proofId: String)
    extends UserProofRequest(db, userId, proofId) with WriteRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    // @todo do not load all steps
    tree.nodes.lastOption.flatMap(_.parent) match {
      case None => new ErrorResponse("Proof does not have any steps yet") :: Nil
      case Some(node) =>
        node.pruneBelow()
        val info = db.getProofInfo(proofId)
        db.updateProofInfo(info.copy(closed = false))
        val item = AgendaItem(node.id.toString, AgendaItem.nameOf(node), proofId, node.allAncestors.map(_.id.toString))
        new PruneBelowResponse(item) :: Nil
    }
  }
}
