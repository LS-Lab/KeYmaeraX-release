/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.AgendaAwesomeResponse
import edu.cmu.cs.ls.keymaerax.hydra.{
  AgendaItem,
  DBAbstraction,
  DbProofTree,
  ProofTree,
  ReadRequest,
  Response,
  UserProofRequest,
}

import scala.collection.immutable.{::, List, Nil}
import spray.json._
import spray.json.DefaultJsonProtocol._

/**
 * Gets the proof root as agenda item (browse a proof from root to leaves).
 *
 * @param db
 *   Access to the database.
 * @param userId
 *   Identifies the user.
 * @param proofId
 *   Identifies the proof.
 */
class GetProofRootAgendaRequest(db: DBAbstraction, userId: String, proofId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree: ProofTree = DbProofTree(db, proofId)
    val agendaItems: List[AgendaItem] = AgendaItem(tree.root.id.toString, AgendaItem.nameOf(tree.root), proofId) :: Nil
    val marginLeft :: marginRight :: Nil = db
      .getConfiguration(userId)
      .config
      .getOrElse("renderMargins", "[40,80]")
      .parseJson
      .convertTo[Array[Int]]
      .toList
    AgendaAwesomeResponse(
      tree.info.modelId.get.toString,
      proofId,
      tree.root,
      tree.root :: Nil,
      agendaItems,
      closed = false,
      marginLeft,
      marginRight,
    ) :: Nil
  }
}
