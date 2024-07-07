/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.bellerophon.IOListeners.CollectProgressListener
import org.keymaerax.bellerophon.{ExhaustiveSequentialInterpreter, IOListener, NamedBelleExpr}
import org.keymaerax.hydra.responses.proofs.RunBelleTermResponse
import org.keymaerax.hydra.{
  BellerophonTacticExecutor,
  DBAbstraction,
  DatabasePopulator,
  DbProofTree,
  ErrorResponse,
  ProofSession,
  ProofTree,
  ReadRequest,
  Response,
  UserProofRequest,
}
import org.keymaerax.parser.ArchiveParser
import spray.json.JsonParser.ParsingException
import spray.json._

import scala.collection.immutable.{List, Nil}

/** Create a proof if it does not exist yet. Read request, so that guest users can check proofs. */
class InitializeProofFromTacticRequest(db: DBAbstraction, userId: String, proofId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    val proofInfo = db.getProofInfo(proofId)
    proofInfo.tactic match {
      case None => new ErrorResponse("Proof " + proofId + " does not have a tactic")
      case Some(_) if proofInfo.modelId.isEmpty =>
        throw new Exception("Proof " + proofId + " does not refer to a model")
      case Some(t) if proofInfo.modelId.isDefined =>
        val proofSession = session(proofId).asInstanceOf[ProofSession]

        import TacticInfoJsonProtocol._
        val tacticText =
          try { t.parseJson.convertTo[TacticInfo].tacticText }
          catch {
            case _: ParsingException => t // @note backwards compatibility with database tactics not in JSON
          }

        val tactic = ArchiveParser.tacticParser(tacticText, proofSession.defs)

        def atomic(name: String): String = {
          val tree: ProofTree = DbProofTree(db, proofId)
          tree.root.runTactic(userId, ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), tactic, name)
        }

        tactic match {
          case n: NamedBelleExpr => RunBelleTermResponse(proofId, "()", atomic(n.name), "")
          case _ =>
            try {
              // @note replace listener created by proof tree (we want a different tactic name for each component of the
              // executed tactic and we want to see progress)
              val interpreter = (_: List[IOListener]) =>
                DatabasePopulator
                  .prepareInterpreter(db, proofId.toInt, proofSession.defs, CollectProgressListener() :: Nil)
              val tree: ProofTree = DbProofTree(db, proofId)
              val executor = BellerophonTacticExecutor.defaultExecutor
              val taskId = tree.root.runTactic(userId, interpreter, tactic, "", executor)
              RunBelleTermResponse(proofId, "()", taskId, "")
            } catch {
              case _: Throwable =>
                // @note if spoonfeeding interpreter fails, try sequential interpreter so that tactics at least proofcheck
                //      even if browsing then shows a single step only
                RunBelleTermResponse(proofId, "()", atomic("custom"), "")
            }
        }
    }
  }
}
