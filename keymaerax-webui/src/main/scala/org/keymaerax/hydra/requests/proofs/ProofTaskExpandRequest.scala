/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.bellerophon.{BelleProvable, ExhaustiveSequentialInterpreter, SpoonFeedingInterpreter}
import org.keymaerax.btactics.DerivationInfoRegistry
import org.keymaerax.hydra.responses.proofs.ExpandTacticResponse
import org.keymaerax.hydra.{
  AgendaItem,
  DBAbstraction,
  DbProofTree,
  ErrorResponse,
  ProofSession,
  ReadRequest,
  RequestHelper,
  Response,
  UserProofRequest,
  VerboseTraceToTacticConverter,
}
import org.keymaerax.infrastruct.Augmentors.SequentAugmentor
import org.keymaerax.parser.ArchiveParser
import org.keymaerax.pt.ProvableSig
import org.keymaerax.tools.qe.{DefaultSMTConverter, KeYmaeraToMathematica}
import spray.json.DefaultJsonProtocol._
import spray.json._

import scala.annotation.nowarn
import scala.collection.immutable.{::, List, Nil}

class ProofTaskExpandRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, strict: Boolean)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  @nowarn("msg=match may not be exhaustive")
  override protected def doResultingResponse(): Response = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => throw new Exception("Unknown node " + nodeId)
      case Some(node) if node.maker.isEmpty =>
        new ErrorResponse(
          "Unable to expand node " + nodeId + " of proof " + proofId + ", because it did not record a tactic"
        )
      case Some(node) if node.maker.isDefined =>
        assert(node.maker.isDefined, "Unable to expand node without tactics")
        val (conjecture, parentStep, parentRule) =
          (ProvableSig.startProof(node.conclusion, tree.info.defs(db)), node.maker.get, node.makerShortName.get)
        val localProofId = db.createProof(conjecture)
        val proofSession = session(proofId).asInstanceOf[ProofSession]
        // @note add a copy of parent proof session under local proof ID to allow stepping deeper into tactics
        session += localProofId.toString -> proofSession.copy(proofId = localProofId.toString)
        val innerInterpreter = SpoonFeedingInterpreter(
          localProofId,
          -1,
          db.createProof,
          proofSession.defs,
          RequestHelper.listenerFactory(db, proofSession),
          ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
          1,
          strict = strict,
          convertPending = false,
          recordInternal = true,
        )
        val parentTactic = ArchiveParser.tacticParser(parentStep, proofSession.defs)
        innerInterpreter(parentTactic, BelleProvable.plain(conjecture))
        innerInterpreter.kill()

        val trace = db.getExecutionTrace(localProofId)
        val marginLeft :: marginRight :: Nil = db
          .getConfiguration(userId)
          .config
          .getOrElse("renderMargins", "[40,80]")
          .parseJson
          .convertTo[Array[Int]]
          .toList
        if (trace.steps.size == 1 && trace.steps.head.rule == parentRule) {
          DerivationInfoRegistry.locate(parentTactic) match {
            case Some(ptInfo) =>
              ExpandTacticResponse(localProofId, Nil, Nil, ptInfo.codeName, "", Nil, Nil, marginLeft, marginRight)
            case None => new ErrorResponse("No further details available")
          }
        } else {
          val innerTree = DbProofTree(db, localProofId.toString).load()
          val (stepDetails, _) = innerTree.tacticString(new VerboseTraceToTacticConverter(innerTree.info.defs(db)))
          val innerSteps = innerTree.nodes
          val agendaItems: List[AgendaItem] = innerTree
            .openGoals
            .map(n => AgendaItem(n.id.toString, AgendaItem.nameOf(n), proofId))
          val goals = innerTree.openGoals.map(_.conclusion)
          val backendGoals = innerTree
            .openGoals
            .map(n =>
              if (n.conclusion.isFOL) Some(
                (KeYmaeraToMathematica(n.conclusion.toFormula).toString, DefaultSMTConverter(n.conclusion.toFormula))
              )
              else None
            )

          ExpandTacticResponse(
            localProofId,
            goals,
            backendGoals,
            parentStep,
            stepDetails,
            innerSteps,
            agendaItems,
            marginLeft,
            marginRight,
          )
        }
    }
  }
}
