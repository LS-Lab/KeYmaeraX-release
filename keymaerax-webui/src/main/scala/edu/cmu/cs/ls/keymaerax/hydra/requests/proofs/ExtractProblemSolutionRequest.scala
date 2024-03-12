/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.ExtractProblemSolutionResponse
import edu.cmu.cs.ls.keymaerax.hydra.{
  ArchiveEntryPrinter,
  DBAbstraction,
  DbProofTree,
  ModelPOJO,
  ProofPOJO,
  ReadRequest,
  RequestHelper,
  Response,
  UserProofRequest,
  VerboseTraceToTacticConverter,
}
import edu.cmu.cs.ls.keymaerax.parser.ParseException

import scala.collection.immutable.{List, Nil}

class ExtractProblemSolutionRequest(db: DBAbstraction, userId: String, proofId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    val proofName = tree.info.name
    val tactic =
      try { tree.tacticString(new VerboseTraceToTacticConverter(tree.info.defs(db)))._1 }
      catch {
        case _: ParseException =>
          // fallback if for whatever reason model or tactic is not parseable: print verbatim without beautification
          RequestHelper.tacticString(tree.info)
      }
    val model = db.getModel(tree.info.modelId.get)

    def getLemmas(tactic: String): List[(String, (Option[ModelPOJO], Option[ProofPOJO]))] = {
      val lemmaFinder = """useLemma\("([^"]*)"""".r
      val lemmaNames = lemmaFinder.findAllMatchIn(tactic).map(m => m.group(1))
      val lemmaModels = lemmaNames.map(n => n -> db.getModelList(userId).find(n == _.name))
      val lemmas = lemmaModels
        .map(m =>
          m._1 ->
            (m._2 match {
              case Some(mp) => db.getProofsForModel(mp.modelId).filter(_.closed) match {
                  case Nil => m._2 -> None
                  case proofs => m._2 -> Some(proofs.maxBy(_.date))
                }
              case _ => m._2 -> None
            })
        )
        .toList
      val parentLemmas: List[(String, (Option[ModelPOJO], Option[ProofPOJO]))] = lemmas.flatMap({ case (_, (mp, pp)) =>
        (mp, pp) match {
          case (Some(m), Some(p)) => p.tactic match {
              case Some(t) => getLemmas(t)
              case _ => Nil
            }
          case _ => Nil
        }
      })

      parentLemmas ++ lemmas
    }

    val lemmas = getLemmas(tactic)
    val printedLemmas = lemmas.map({
      case (_, (Some(modelPOJO), proofPOJO)) => ArchiveEntryPrinter.archiveEntry(
          modelPOJO,
          proofPOJO match {
            case Some(p) => (p.name -> p.tactic.getOrElse("/* todo */ nil")) :: Nil
            case None => ("Todo" -> "/* todo */ nil") :: Nil
          },
          withComments = true,
        )
      case (lemmaName, (None, _)) => s"""Lemma "$lemmaName" /* todo */ End."""
    })
    val modelContent = ArchiveEntryPrinter.archiveEntry(model, (proofName, tactic) :: Nil, withComments = true)
    val archiveContent = printedLemmas.mkString("\n\n") ++ modelContent
    new ExtractProblemSolutionResponse(archiveContent) :: Nil
  }
}
