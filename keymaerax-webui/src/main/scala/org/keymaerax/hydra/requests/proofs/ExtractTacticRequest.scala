/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.responses.proofs.GetTacticResponse
import org.keymaerax.hydra.{
  DBAbstraction,
  DbProofTree,
  LabelledTraceToTacticConverter,
  ProofPOJO,
  Response,
  UserProofRequest,
  VerboseTraceToTacticConverter,
  WriteRequest,
}

class ExtractTacticRequest(db: DBAbstraction, userId: String, proofIdStr: String, verbose: Boolean)
    extends UserProofRequest(db, userId, proofIdStr) with WriteRequest {
  override def doResultingResponse(): Response = {
    val tree = DbProofTree(db, proofIdStr)
    val (tactic, locInfoSrc) = tree.tacticString(
      if (verbose) new VerboseTraceToTacticConverter(tree.info.defs(db))
      else new LabelledTraceToTacticConverter(tree.info.defs(db))
    )
    // remember tactic string
    val locInfo = locInfoSrc.map({ case (k, v) => (k, v.id.toString) })
    val newInfo = ProofPOJO(
      tree.info.proofId,
      tree.info.modelId,
      tree.info.name,
      tree.info.description,
      tree.info.date,
      tree.info.stepCount,
      tree.info.closed,
      tree.info.provableId,
      tree.info.temporary,
      Some(GetTacticResponse(tactic, locInfo).getJson.compactPrint),
    )
    db.updateProofInfo(newInfo)
    GetTacticResponse(tactic, locInfo)
  }
}
