/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.btactics.macros.{CoreAxiomInfo, DerivedAxiomInfo, ProvableInfo}
import org.keymaerax.hydra.responses.proofs.LemmasResponse
import org.keymaerax.hydra.{DBAbstraction, ReadRequest, Response, UserProofRequest}
import org.keymaerax.infrastruct.Position

class GetLemmasRequest(
    db: DBAbstraction,
    userId: String,
    proofId: String,
    nodeId: String,
    pos: Position,
    partialLemmaName: String,
) extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    val infos = ProvableInfo
      .allInfo
      .filter({ case (name, i) =>
        (i.isInstanceOf[CoreAxiomInfo] || i.isInstanceOf[DerivedAxiomInfo]) &&
        i.canonicalName.contains(partialLemmaName)
      })
      .toList
      .map(_._2)
    LemmasResponse(infos)
  }
}
