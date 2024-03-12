/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.ApplicableAxiomsResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, DbProofTree, ReadRequest, Response, UserProofRequest}
import edu.cmu.cs.ls.keymaerax.infrastruct.Position

import scala.collection.immutable.{List, Map, Nil}

class GetApplicableTwoPosTacticsRequest(
    db: DBAbstraction,
    userId: String,
    proofId: String,
    nodeId: String,
    pos1: Position,
    pos2: Position,
) extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    if (tree.done) return ApplicableAxiomsResponse(Nil, Map.empty, topLevel = true) :: Nil
    tree.locate(nodeId).map(n => n.applicableTacticsAt(pos1, Some(pos2))) match {
      case None => ApplicableAxiomsResponse(Nil, Map.empty, topLevel = true) :: Nil
      case Some(tactics) => ApplicableAxiomsResponse(tactics, Map.empty, pos1.isTopLevel) :: Nil
    }
  }
}
