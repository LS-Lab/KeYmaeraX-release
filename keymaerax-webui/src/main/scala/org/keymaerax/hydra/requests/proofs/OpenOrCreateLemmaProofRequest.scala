/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.core.StaticSemantics
import org.keymaerax.hydra.{
  CreatedIdResponse,
  DBAbstraction,
  DbProofTree,
  ErrorResponse,
  ProofSession,
  ProofTree,
  Response,
  UserRequest,
  WriteRequest,
}
import org.keymaerax.infrastruct.Augmentors.SequentAugmentor
import org.keymaerax.parser.{
  Declaration,
  KeYmaeraXArchivePrinter,
  Name,
  ParsedArchiveEntry,
  PrettierPrintFormatProvider,
}

import scala.collection.immutable.{::, Map, Nil}

class OpenOrCreateLemmaProofRequest(
    db: DBAbstraction,
    userId: String,
    lemmaName: String,
    parentProofId: String,
    parentTaskId: String,
) extends UserRequest(userId, _ => true) with WriteRequest {
  def resultingResponse(): Response = {
    val modelId: Int = db.getModelList(userId).find(_.name == lemmaName) match {
      case Some(model) => model.modelId
      case None =>
        val tree: ProofTree = DbProofTree(db, parentProofId)
        tree.locate(parentTaskId) match {
          case None => return new ErrorResponse("Unknown node " + parentTaskId + " in proof " + parentProofId)
          case Some(node) if node.goal.isEmpty =>
            return new ErrorResponse("Node " + parentTaskId + " does not have a goal")
          case Some(node) if node.goal.isDefined =>
            val goal = node.goal.get.toFormula
            val proofSession = session(parentProofId).asInstanceOf[ProofSession]
            val symbols = StaticSemantics.symbols(goal)
            val defs = proofSession
              .defs
              .decls
              .filter({ case (Name(n, i), _) => symbols.exists(s => s.name == n && s.index == i) })
            val lemma = ParsedArchiveEntry(lemmaName, "lemma", "", "", Declaration(defs), goal, Nil, Nil, Map.empty)
            val fileContents = new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80))(lemma)

            db.createModel(userId, lemmaName, fileContents, currentDate(), None, None, None).get
        }
    }
    val modelProofs = db.getProofsForModel(modelId)
    val proofId = modelProofs.find(_.closed) match {
      case Some(proof) => proof.proofId
      case None => modelProofs match {
          case head :: _ => head.proofId
          case Nil => db.createProofForModel(modelId, "Proof of " + lemmaName, "", currentDate(), None)
        }
    }
    CreatedIdResponse(proofId.toString)
  }
}
