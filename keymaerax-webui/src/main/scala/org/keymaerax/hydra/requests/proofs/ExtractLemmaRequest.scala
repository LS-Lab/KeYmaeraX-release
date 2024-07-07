/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.responses.proofs.ExtractProblemSolutionResponse
import org.keymaerax.hydra.{
  DBAbstraction,
  DbProofTree,
  ReadRequest,
  Response,
  UserProofRequest,
  VerboseTraceToTacticConverter,
}
import org.keymaerax.lemma.Lemma
import org.keymaerax.tools.ToolEvidence

import scala.collection.immutable.{List, Nil}

class ExtractLemmaRequest(db: DBAbstraction, userId: String, proofId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    val tree = DbProofTree(db, proofId)
    tree.load()
    val model = db.getModel(tree.info.modelId.get)
    val (tactic, _) = tree.tacticString(new VerboseTraceToTacticConverter(model.defs))
    val provable = tree.root.provable
    val evidence = Lemma.requiredEvidence(
      provable,
      ToolEvidence(List("tool" -> "KeYmaera X", "model" -> model.keyFile, "tactic" -> tactic)) :: Nil,
    )
    new ExtractProblemSolutionResponse(new Lemma(provable, evidence, Some(tree.info.name)).toString)
  }
}
