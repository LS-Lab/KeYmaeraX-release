/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.responses.proofs.ApplicableAxiomsResponse
import org.keymaerax.hydra.{DBAbstraction, DbProofTree, ReadRequest, Response, UserProofRequest}
import org.keymaerax.infrastruct.Position

import scala.collection.immutable.{Map, Nil}

class GetApplicableTwoPosTacticsRequest(
    db: DBAbstraction,
    userId: String,
    proofId: String,
    nodeId: String,
    pos1: Position,
    pos2: Position,
) extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    val tree = DbProofTree(db, proofId)
    if (tree.done) return ApplicableAxiomsResponse(Nil, Map.empty, topLevel = true)
    tree.locate(nodeId).map(n => n.applicableTacticsAt(pos1, Some(pos2))) match {
      case None => ApplicableAxiomsResponse(Nil, Map.empty, topLevel = true)
      case Some(tactics) => ApplicableAxiomsResponse(tactics, Map.empty, pos1.isTopLevel)
    }
  }
}
