/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.bellerophon.UIIndex
import org.keymaerax.btactics.macros.DerivationInfo
import org.keymaerax.hydra.responses.proofs.ApplicableAxiomsResponse
import org.keymaerax.hydra.{DBAbstraction, ReadRequest, Response, UserProofRequest}

import scala.collection.immutable.Map
import scala.util.Try

class GetDerivationInfoRequest(db: DBAbstraction, userId: String, proofId: String, axiomId: Option[String])
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    val infos = axiomId match {
      case Some(aid) =>
        val di = Try(DerivationInfo.ofCodeName(aid)).toOption
        di.map(info => (info, UIIndex.comfortOf(aid))).toList
      case None => DerivationInfo.allInfo.map({ case (_, di) => (di, UIIndex.comfortOf(di.codeName)) }).toList
    }
    ApplicableAxiomsResponse(infos, Map.empty, topLevel = true)
  }
}
