/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.bellerophon.ExhaustiveSequentialInterpreter
import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.AgendaAwesomeResponse
import edu.cmu.cs.ls.keymaerax.hydra.{
  AgendaItem,
  DBAbstraction,
  DbProofTree,
  ProofSession,
  ReadRequest,
  RequestHelper,
  Response,
  UserProofRequest,
}
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import spray.json._
import spray.json.DefaultJsonProtocol._

import scala.collection.immutable.{::, List, Nil}
import scala.util.Try

/** Gets all tasks of the specified proof. A task is some work the user has to do. It is not a KeYmaera task! */
class GetAgendaAwesomeRequest(db: DBAbstraction, userId: String, proofId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    // reapply lemmas (may have proved in the mean time)
    val proofSession = session(proofId).asInstanceOf[ProofSession]
    val tree = DbProofTree(db, proofId)
    val leaves = tree.leaves
    val openGoals = leaves.filter(!_.isProved)
    openGoals
      .filter(n => n.maker.exists(_.startsWith("useLemma")) && !n.isProved)
      .foreach(n =>
        n.parent
          .map(p => {
            p.pruneBelow()
            p.runTactic(
              userId,
              ExhaustiveSequentialInterpreter(_, throwWithDebugInfo = false),
              ArchiveParser.tacticParser(n.maker.get, proofSession.defs),
              n.maker.get,
              wait = true,
            )
          })
      )

    val marginLeft :: marginRight :: Nil = db
      .getConfiguration(userId)
      .config
      .getOrElse("renderMargins", "[40,80]")
      .parseJson
      .convertTo[Array[Int]]
      .toList

    // Goals in web UI
    val agendaItems: List[AgendaItem] = openGoals.map(n => AgendaItem(n.id.toString, AgendaItem.nameOf(n), proofId))
    // add unexpanded functions, predicates, programs of the open goals of all leaves to the proof session
    session(proofId) = leaves.flatMap(_.parent).foldLeft(proofSession)(RequestHelper.updateProofSessionDefinitions)
    // @note tree.isProved creates a merged provable, which cannot (yet) succeed when constifications (e.g., dIRule) are not proved (yet)
    val isProved = Try(tree.isProved).toOption.getOrElse(false)
    AgendaAwesomeResponse(
      tree.info.modelId.get.toString,
      proofId,
      tree.root,
      leaves,
      agendaItems,
      isProved,
      marginLeft,
      marginRight,
    ) :: Nil
  }
}
