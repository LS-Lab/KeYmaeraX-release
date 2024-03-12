/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.NodeChildrenResponse
import edu.cmu.cs.ls.keymaerax.hydra.{
  DBAbstraction,
  DbProofTree,
  ErrorResponse,
  ReadRequest,
  Response,
  UserProofRequest,
}

import scala.collection.immutable.{::, List, Nil}
import spray.json._
import spray.json.DefaultJsonProtocol._

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

  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => new ErrorResponse("Unknown node " + nodeId) :: Nil
      case Some(node) =>
        val marginLeft :: marginRight :: Nil = db
          .getConfiguration(userId)
          .config
          .getOrElse("renderMargins", "[40,80]")
          .parseJson
          .convertTo[Array[Int]]
          .toList
        NodeChildrenResponse(proofId, node, marginLeft, marginRight) :: Nil
    }
  }
}
