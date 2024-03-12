/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, ExhaustiveSequentialInterpreter, SpoonFeedingInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics.DerivationInfoRegistry
import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.ExpandTacticResponse
import edu.cmu.cs.ls.keymaerax.hydra.{
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
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.SequentAugmentor
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.qe.{DefaultSMTConverter, KeYmaeraToMathematica}

import scala.collection.immutable.{::, List, Nil}
import spray.json._
import spray.json.DefaultJsonProtocol._

class ProofTaskExpandRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, strict: Boolean)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => throw new Exception("Unknown node " + nodeId)
      case Some(node) if node.maker.isEmpty =>
        new ErrorResponse(
          "Unable to expand node " + nodeId + " of proof " + proofId + ", because it did not record a tactic"
        ) :: Nil
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
              ExpandTacticResponse(localProofId, Nil, Nil, ptInfo.codeName, "", Nil, Nil, marginLeft, marginRight) ::
                Nil
            case None => new ErrorResponse("No further details available") :: Nil
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
          ) :: Nil
        }
    }
  }
}
