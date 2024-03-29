/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.bellerophon.UIIndex
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfo
import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.ApplicableAxiomsResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ReadRequest, Response, UserProofRequest}

import scala.collection.immutable.{List, Map, Nil}
import scala.util.Try

class GetDerivationInfoRequest(db: DBAbstraction, userId: String, proofId: String, axiomId: Option[String])
  extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val infos = axiomId match {
      case Some(aid) =>
        val di = Try(DerivationInfo.ofCodeName(aid)).toOption
        di.map(info => (info, UIIndex.comfortOf(aid))).toList
      case None => DerivationInfo.allInfo.
        map({case (_, di) => (di, UIIndex.comfortOf(di.codeName))}).toList
    }
    ApplicableAxiomsResponse(infos, Map.empty, topLevel=true) :: Nil
  }
}
