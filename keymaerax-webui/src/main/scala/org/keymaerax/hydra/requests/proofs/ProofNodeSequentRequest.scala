/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.responses.proofs.ProofNodeSequentResponse
import org.keymaerax.hydra.{DBAbstraction, DbProofTree, ReadRequest, Response, UserProofRequest}
import spray.json.DefaultJsonProtocol._
import spray.json._

import scala.collection.immutable.{::, Nil}

class ProofNodeSequentRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case None => throw new Exception("Unknown node " + nodeId)
      case Some(node) =>
        val marginLeft :: marginRight :: Nil = db
          .getConfiguration(userId)
          .config
          .getOrElse("renderMargins", "[40,80]")
          .parseJson
          .convertTo[Array[Int]]
          .toList
        ProofNodeSequentResponse(proofId, node, marginLeft, marginRight)
    }
  }
}
