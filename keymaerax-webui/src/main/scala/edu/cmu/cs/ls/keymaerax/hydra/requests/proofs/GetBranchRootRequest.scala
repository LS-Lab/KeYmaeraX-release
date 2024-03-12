/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.responses.proofs.GetBranchRootResponse
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

case class GetBranchRootRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponses(): List[Response] = {
    val tree = DbProofTree(db, proofId)
    var currNode = tree.locate(nodeId)
    var done = false
    while (currNode.flatMap(_.parent).nonEmpty && !done) {
      currNode = currNode.flatMap(_.parent)
      /* Don't stop at the first node just because it branches (it may be the end of one branch and the start of the
       * next), but if we see branching anywhere else we've found the end of our branch. */
      done = currNode.get.children.size > 1
    }
    currNode match {
      case None => new ErrorResponse("Unknown node " + nodeId) :: Nil
      case Some(n) =>
        val marginLeft :: marginRight :: Nil = db
          .getConfiguration(userId)
          .config
          .getOrElse("renderMargins", "[40,80]")
          .parseJson
          .convertTo[Array[Int]]
          .toList
        new GetBranchRootResponse(n, marginLeft, marginRight) :: Nil
    }

  }
}
