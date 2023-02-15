/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.bellerophon.ExhaustiveSequentialInterpreter
import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.AgendaAwesomeResponse
import edu.cmu.cs.ls.keymaerax.hydra.{AgendaItem, DBAbstraction, DbProofTree, ProofSession, ProofTree, ReadRequest, RequestHelper, Response, UserProofRequest}
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import spray.json._
import spray.json.DefaultJsonProtocol._

import scala.collection.immutable.{::, List, Nil}

/** Gets all tasks of the specified proof. A task is some work the user has to do. It is not a KeYmaera task! */
class GetAgendaAwesomeRequest(db: DBAbstraction, userId: String, proofId: String) extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    // reapply lemmas (may have proved in the mean time)
    val proofSession = session(proofId).asInstanceOf[ProofSession]
    DbProofTree(db, proofId).openGoals.
      filter(n => n.maker.exists(_.startsWith("useLemma")) && !n.isProved).
      foreach(n => n.parent.map(p => {
        p.pruneBelow()
        p.runTactic(userId, ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false), ArchiveParser.tacticParser(n.maker.get, proofSession.defs), n.maker.get, wait = true)
      }))

    val tree: ProofTree = DbProofTree(db, proofId)
    val leaves = tree.leaves
    val closed = tree.isProved

    val marginLeft::marginRight::Nil = db.getConfiguration(userId).config.getOrElse("renderMargins", "[40,80]").parseJson.convertTo[Array[Int]].toList

    // Goals in web UI
    val agendaItems: List[AgendaItem] = leaves.
      filterNot(_.isProved).
      map(n => AgendaItem(n.id.toString, AgendaItem.nameOf(n), proofId))
    // add unexpanded functions, predicates, programs of the open goals of all leaves to the proof session
    session(proofId) = leaves.flatMap(_.parent).foldLeft(proofSession)(RequestHelper.updateProofSessionDefinitions)
    AgendaAwesomeResponse(tree.info.modelId.get.toString, proofId, tree.root, leaves, agendaItems, closed, marginLeft, marginRight) :: Nil
  }
}