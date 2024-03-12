/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.ExtractProblemSolutionResponse
import edu.cmu.cs.ls.keymaerax.parser.ParseException

import scala.collection.immutable.{List, Nil}

class ExtractModelSolutionsRequest(
    db: DBAbstraction,
    userId: String,
    modelIds: List[Int],
    withProofs: Boolean,
    exportEmptyProof: Boolean,
) extends UserRequest(userId, _ => true) with ReadRequest {
  override def resultingResponses(): List[Response] = {
    def printProof(tree: ProofTree, model: ModelPOJO): String =
      try { tree.tacticString(new VerboseTraceToTacticConverter(model.defs))._1 }
      catch { case _: ParseException => RequestHelper.tacticString(tree.info) }

    def modelProofs(model: ModelPOJO): List[(String, String)] = {
      if (withProofs) db
        .getProofsForModel(model.modelId)
        .map(p => p.name -> printProof(DbProofTree(db, p.proofId.toString), model))
      else Nil
    }
    val models = modelIds
      .map(mid => {
        val model = db.getModel(mid)
        model -> modelProofs(model)
      })
      .filter(exportEmptyProof || _._2.nonEmpty)
    val archiveContent = models
      .map({ case (model, proofs) => ArchiveEntryPrinter.archiveEntry(model, proofs, withComments = true) })
      .mkString("\n\n")
    new ExtractProblemSolutionResponse(archiveContent + "\n") :: Nil
  }
}
