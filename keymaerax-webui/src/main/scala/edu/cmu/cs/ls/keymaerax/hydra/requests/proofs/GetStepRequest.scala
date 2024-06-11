/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.bellerophon.UIIndex
import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.ApplicableAxiomsResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, DbProofTree, ProofSession, ReadRequest, Response, UserProofRequest}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.SequentAugmentor
import edu.cmu.cs.ls.keymaerax.infrastruct.Position

import scala.collection.immutable.{Map, Nil}

class GetStepRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, pos: Position)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId).flatMap(_.goal) match {
      case None => ApplicableAxiomsResponse(Nil, Map.empty, pos.isTopLevel)
      case Some(goal) => goal.sub(pos) match {
          case Some(fml: Formula) =>
            val substs = session(proofId) match {
              case ps: ProofSession => ps.defs.substs
              case _ => Nil
            }
            UIIndex.theStepAt(fml, Some(pos), None, substs) match {
              case Some(step) => ApplicableAxiomsResponse((step, None) :: Nil, Map.empty, pos.isTopLevel)
              case None => ApplicableAxiomsResponse(Nil, Map.empty, pos.isTopLevel)
            }
          case _ => ApplicableAxiomsResponse(Nil, Map.empty, pos.isTopLevel)
        }
    }
  }
}
