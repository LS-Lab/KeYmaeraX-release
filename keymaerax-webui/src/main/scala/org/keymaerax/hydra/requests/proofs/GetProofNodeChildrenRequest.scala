/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.responses.proofs.NodeChildrenResponse
import org.keymaerax.hydra.{DBAbstraction, DbProofTree, ErrorResponse, ReadRequest, Response, UserProofRequest}
import spray.json.DefaultJsonProtocol._
import spray.json._

import scala.collection.immutable.{::, Nil}

/**
 * Gets the children of a proof node (browse a proof from root to leaves).
 *
 * @param db
 *   Access to the database.
 * @param userId
 *   Identifies the user.
 * @param proofId
 *   Identifies the proof.
 * @param nodeId
 *   Identifies the proof node.
 */
class GetProofNodeChildrenRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {

  override protected def doResultingResponse(): Response = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => new ErrorResponse("Unknown node " + nodeId)
      case Some(node) =>
        val marginLeft :: marginRight :: Nil = db
          .getConfiguration(userId)
          .config
          .getOrElse("renderMargins", "[40,80]")
          .parseJson
          .convertTo[Array[Int]]
          .toList
        NodeChildrenResponse(proofId, node, marginLeft, marginRight)
    }
  }
}
