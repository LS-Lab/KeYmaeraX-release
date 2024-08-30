/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.GlobalState
import org.keymaerax.core.{Formula, Sequent}
import org.keymaerax.hydra.responses.proofs.ProofLemmasResponse
import org.keymaerax.hydra.{DBAbstraction, ModelPOJO, ProofPOJO, ReadRequest, Response, UserProofRequest}
import org.keymaerax.lemma.LemmaDBFactory

import java.io.File
import scala.collection.immutable.{IndexedSeq, List, Nil}

class GetProofLemmasRequest(db: DBAbstraction, userId: String, proofId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    def collectLemmaNames(tactic: String): List[String] = {
      """useLemma(At)?\("(?<lemmaName>[^"]+)"""".r.findAllMatchIn(tactic).map(m => m.group("lemmaName")).toList
    }

    /** Recursively required lemmas in the order they ought to be proved. */
    def recCollectRequiredLemmaNames(proofId: Int, collectedLemmas: List[(String, Int)]): List[(String, Int)] = {
      val proofInfo = db.getProofInfo(proofId)
      val lemmaNames = (proofInfo.tactic.map(collectLemmaNames).getOrElse(Nil).toSet -- collectedLemmas.map(_._1).toSet)
        .toList
      val models = db.getModelList(userId).filter(m => lemmaNames.contains(m.name))
      val lemmaProofs: List[(ModelPOJO, ProofPOJO)] = models.flatMap(m => {
        val proofs = db.getProofsForModel(m.modelId)
        proofs.find(_.tactic.isDefined) match {
          case None => proofs.headOption.map(m -> _)
          case p => p.map(m -> _)
        }
      })
      // @note check non-existent or outdated lemmas
      val unprovedLemmas = lemmaProofs.filter(e =>
        LemmaDBFactory.lemmaDB.get("user" + File.separator + e._1.name) match {
          case Some(l) =>
            val lemmaConc = e._1.defs.exhaustiveSubst(l.fact.conclusion)
            val modelConc = e
              ._1
              .defs
              .exhaustiveSubst(Sequent(
                IndexedSeq(),
                IndexedSeq(GlobalState.archiveParser(e._1.keyFile).head.model.asInstanceOf[Formula]),
              ))
            lemmaConc != modelConc // outdated or unexpected if different conclusion
          case None => true
        }
      )
      (unprovedLemmas.foldRight(collectedLemmas)({ case ((_, p), cl) =>
        recCollectRequiredLemmaNames(p.proofId, cl) ++ cl
      }) ++ unprovedLemmas.map({ case (m, p) => (m.name, p.proofId) })).distinct
    }

    val lemmaNames = recCollectRequiredLemmaNames(proofId.toInt, Nil)
    ProofLemmasResponse(lemmaNames)
  }
}
