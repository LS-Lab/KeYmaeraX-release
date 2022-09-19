/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.GenProduct
import edu.cmu.cs.ls.keymaerax.btactics.{ConfigurableGenerator, TactixInit, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core.{CoreException, Expression, Formula, Program, insist}
import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.OpenProofResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ErrorResponse, PossibleAttackResponse, ProofSession, ReadRequest, Response, UserRequest}
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, Parser}

import scala.collection.immutable.{List, Map, Nil, Seq}
import scala.util.Try

class OpenProofRequest(db: DBAbstraction, userId: String, proofId: String, wait: Boolean = false)
//@note do not extend UserProofRequest since we are opening a proof which may not exist and we want a better error message
  extends UserRequest(userId, (id: String) => Try(proofId.toInt).toOption.isDefined) with ReadRequest {
  override final def resultingResponses(): List[Response] = {
    if (db.proofExists(proofId.toInt)) {
      assert(db.getProofInfo(proofId).modelId.isEmpty || db.userOwnsProof(userId, proofId))
      val proofInfo = db.getProofInfo(proofId)
      val modelId = proofInfo.modelId
      if (modelId.isEmpty) throw new Exception("Database consistency error: unable to open proof " + proofId + ", because it does not refer to a model")
      else if (db.getModel(modelId.get).userId != userId) new PossibleAttackResponse("Permission denied")::Nil
      else {
        insist(db.getModel(proofInfo.modelId.getOrElse(throw new CoreException(s"Cannot open a proof without model, proofId=$proofId"))).userId == userId, s"User $userId does not own the model associated with proof $proofId")

        proofInfo.modelId match {
          case None => new ErrorResponse("Unable to open proof " + proofId + ", because it does not refer to a model")::Nil // duplicate check to above
          case Some(mId) =>
            var products: Map[Expression, Seq[GenProduct]] = Map[Expression, Seq[GenProduct]]()
            Parser.parser.setAnnotationListener((p: Program, inv: Formula) =>
              products += (p -> (products.getOrElse(p, Nil) :+ (inv, None))))
            val problem = ArchiveParser.parseProblem(db.getModel(mId).keyFile)
            //@note add unexpanded (but elaborated) form, and fully expanded form to generator; generator itself also uses unification
            val generator = ConfigurableGenerator.create(products, problem.defs)
            session += proofId -> ProofSession(proofId, TactixLibrary.invGenerator, generator, problem.defs)
            TactixInit.invSupplier = generator
            OpenProofResponse(proofInfo, "loaded" /*TaskManagement.TaskLoadStatus.Loaded.toString.toLowerCase()*/) :: Nil
        }
      }
    } else {
      new ErrorResponse("Proof does not exist") :: Nil
    }
  }
}