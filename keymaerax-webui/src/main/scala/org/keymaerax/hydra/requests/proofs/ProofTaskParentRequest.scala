/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.responses.proofs.ProofTaskNodeResponse
import org.keymaerax.hydra.{DBAbstraction, DbProofTree, ErrorResponse, ReadRequest, Response, UserProofRequest}
import spray.json.DefaultJsonProtocol._
import spray.json._

import scala.collection.immutable.{::, Nil}

class ProofTaskParentRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId).flatMap(_.parent) match {
      case Some(parent) =>
        val marginLeft :: marginRight :: Nil = db
          .getConfiguration(userId)
          .config
          .getOrElse("renderMargins", "[40,80]")
          .parseJson
          .convertTo[Array[Int]]
          .toList
        new ProofTaskNodeResponse(parent, marginLeft, marginRight)
      case None => new ErrorResponse("Cannot get parent of node " + nodeId + ", node might be unknown or root")
    }
  }
}
