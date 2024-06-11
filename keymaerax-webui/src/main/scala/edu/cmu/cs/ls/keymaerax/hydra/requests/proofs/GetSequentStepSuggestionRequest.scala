/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.bellerophon.Fixed
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfo
import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.ApplicableAxiomsResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, DbProofTree, ReadRequest, Response, UserProofRequest}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.SequentAugmentor
import edu.cmu.cs.ls.keymaerax.infrastruct.SuccPosition

import scala.collection.immutable.{Map, Nil}

class GetSequentStepSuggestionRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => ApplicableAxiomsResponse(Nil, Map.empty, topLevel = true)
      case Some(node) => node.goal match {
          case None => ApplicableAxiomsResponse(Nil, Map.empty, topLevel = true) // @note node closed
          case Some(seq) =>
            if (seq.isFOL) {
              val folSuggestions = "QE" :: "abbrv" :: "hideL" :: Nil
              // todo: counterexample, find assumptions + general help
              val tactics = folSuggestions.map(s => (DerivationInfo(s), None))
              ApplicableAxiomsResponse(tactics, Map.empty, topLevel = true)
            } else {
              // find "largest" succedent formula with programs and suggest top-level popup content
              val pos = SuccPosition(1)
              ApplicableAxiomsResponse(
                node.applicableTacticsAt(pos),
                node.tacticInputSuggestions(pos),
                topLevel = true,
                Some(Fixed(1)),
              )
            }
        }
    }
  }
}
