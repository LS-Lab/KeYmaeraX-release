/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.btactics.macros.{CoreAxiomInfo, DerivedAxiomInfo, ProvableInfo}
import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.LemmasResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ReadRequest, Response, UserProofRequest}
import edu.cmu.cs.ls.keymaerax.infrastruct.Position

import scala.collection.immutable.{List, Nil}

class GetLemmasRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, pos: Position,
                       partialLemmaName: String) extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val infos = ProvableInfo.allInfo.filter({case (name, i) =>
      (i.isInstanceOf[CoreAxiomInfo] || i.isInstanceOf[DerivedAxiomInfo]) && i.canonicalName.contains(partialLemmaName)})
      .toList.map(_._2)
    LemmasResponse(infos)::Nil
  }
}
