/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.btactics.{ConfigurableGenerator, Invariant, TactixInit, TactixLibrary}
import org.keymaerax.core.{insist, CoreException, Expression, Formula, Program}
import org.keymaerax.hydra.responses.proofs.OpenProofResponse
import org.keymaerax.hydra.{
  DBAbstraction,
  ErrorResponse,
  PossibleAttackResponse,
  ProofSession,
  ReadRequest,
  Response,
  UserRequest,
}
import org.keymaerax.parser.{ArchiveParser, Parser}

import scala.collection.immutable.{Map, Nil, Seq}
import scala.util.Try

class OpenProofRequest(db: DBAbstraction, userId: String, proofId: String, wait: Boolean = false)
//@note do not extend UserProofRequest since we are opening a proof which may not exist and we want a better error message
    extends UserRequest(userId, (id: String) => Try(proofId.toInt).toOption.isDefined) with ReadRequest {
  override final def resultingResponse(): Response = {
    if (db.proofExists(proofId.toInt)) {
      assert(db.getProofInfo(proofId).modelId.isEmpty || db.userOwnsProof(userId, proofId))
      val proofInfo = db.getProofInfo(proofId)
      val modelId = proofInfo.modelId
      if (modelId.isEmpty) throw new Exception(
        "Database consistency error: unable to open proof " + proofId + ", because it does not refer to a model"
      )
      else if (db.getModel(modelId.get).userId != userId) new PossibleAttackResponse("Permission denied")
      else {
        insist(
          db.getModel(
              proofInfo
                .modelId
                .getOrElse(throw new CoreException(s"Cannot open a proof without model, proofId=$proofId"))
            )
            .userId == userId,
          s"User $userId does not own the model associated with proof $proofId",
        )

        proofInfo.modelId match {
          case None =>
            // duplicate check to above
            new ErrorResponse("Unable to open proof " + proofId + ", because it does not refer to a model")
          case Some(mId) =>
            var products: Map[Expression, Seq[Invariant]] = Map[Expression, Seq[Invariant]]()
            Parser
              .parser
              .setAnnotationListener((p: Program, inv: Formula) =>
                products += (p -> (products.getOrElse(p, Nil) :+ Invariant(inv)))
              )
            val problem = ArchiveParser.parseProblem(db.getModel(mId).keyFile)
            // @note add unexpanded (but elaborated) form, and fully expanded form to generator; generator itself also uses unification
            val generator = ConfigurableGenerator.create(products, problem.defs)
            session += proofId -> ProofSession(proofId, TactixLibrary.invGenerator, generator, problem.defs)
            TactixInit.invSupplier = generator
            OpenProofResponse(proofInfo, "loaded" /*TaskManagement.TaskLoadStatus.Loaded.toString.toLowerCase()*/ )
        }
      }
    } else { new ErrorResponse("Proof does not exist") }
  }
}
