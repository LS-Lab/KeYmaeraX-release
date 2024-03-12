/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.{
  DBAbstraction,
  DbProofTree,
  ErrorResponse,
  KvpResponse,
  ReadRequest,
  Response,
  UserProofRequest,
}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.SequentAugmentor
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence

import scala.collection.immutable.{List, Nil}

class ExportCurrentSubgoal(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    DbProofTree(db, proofId).locate(nodeId).flatMap(_.goal) match {
      case None => new ErrorResponse("Unknown node " + nodeId) :: Nil
      case Some(goal) =>
        val provable = ProvableSig.startPlainProof(goal)
        val lemma = Lemma.apply(provable, List(ToolEvidence(List("tool" -> "mock"))), None)
        new KvpResponse(
          "sequent",
          "Sequent: \n" + goal.toString + "\n\nFormula: \n" + goal.toFormula.prettyString + "\n\nProvable: \n" +
            provable.prettyString + "\n\nLemma:\n" + lemma.toString,
        ) :: Nil
    }
  }
}
