/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.hydra.responses.proofs.GetPathAllResponse
import org.keymaerax.hydra.{DBAbstraction, DbProofTree, ProofTreeNode, ReadRequest, Response, UserProofRequest}
import spray.json.DefaultJsonProtocol._
import spray.json._

import scala.collection.immutable.{::, List, Nil}

case class GetPathAllRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    val tree = DbProofTree(db, proofId)
    tree.load()
    var node: Option[ProofTreeNode] = tree.locate(nodeId)
    var path: List[ProofTreeNode] = Nil
    while (node.nonEmpty) {
      path = node.get :: path
      node = node.get.parent
    }
    val parentsRemaining = 0
    val marginLeft :: marginRight :: Nil = db
      .getConfiguration(userId)
      .config
      .getOrElse("renderMargins", "[40,80]")
      .parseJson
      .convertTo[Array[Int]]
      .toList
    new GetPathAllResponse(path.reverse, parentsRemaining, marginLeft, marginRight)
  }
}
