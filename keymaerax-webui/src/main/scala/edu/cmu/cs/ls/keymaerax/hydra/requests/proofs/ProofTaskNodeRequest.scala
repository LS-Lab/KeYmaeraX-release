/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.ProofTaskNodeResponse
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

class ProofTaskNodeRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    tree.locate(nodeId) match {
      case Some(node) =>
        val marginLeft :: marginRight :: Nil = db
          .getConfiguration(userId)
          .config
          .getOrElse("renderMargins", "[40,80]")
          .parseJson
          .convertTo[Array[Int]]
          .toList
        new ProofTaskNodeResponse(node, marginLeft, marginRight) :: Nil
      case None => new ErrorResponse("Cannot get parent of node " + nodeId + ", node might be unknown or root") :: Nil
    }
  }
}
