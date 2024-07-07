/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.{
  DBAbstraction,
  DbProofTree,
  ErrorResponse,
  KvpResponse,
  ReadRequest,
  Response,
  UserProofRequest,
}
import org.keymaerax.infrastruct.Augmentors.SequentAugmentor
import org.keymaerax.lemma.Lemma
import org.keymaerax.pt.ProvableSig
import org.keymaerax.tools.ToolEvidence

class ExportCurrentSubgoal(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    DbProofTree(db, proofId).locate(nodeId).flatMap(_.goal) match {
      case None => new ErrorResponse("Unknown node " + nodeId)
      case Some(goal) =>
        val provable = ProvableSig.startPlainProof(goal)
        val lemma = Lemma.apply(provable, List(ToolEvidence(List("tool" -> "mock"))), None)
        new KvpResponse(
          "sequent",
          "Sequent: \n" + goal.toString + "\n\nFormula: \n" + goal.toFormula.prettyString + "\n\nProvable: \n" +
            provable.prettyString + "\n\nLemma:\n" + lemma.toString,
        )
    }
  }
}
