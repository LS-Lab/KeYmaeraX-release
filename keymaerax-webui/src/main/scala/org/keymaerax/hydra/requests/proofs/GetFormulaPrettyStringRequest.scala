/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.proofs

import org.keymaerax.core.Expression
import org.keymaerax.hydra.{
  DBAbstraction,
  DbProofTree,
  ErrorResponse,
  PlainResponse,
  ReadRequest,
  Response,
  UserProofRequest,
}
import org.keymaerax.infrastruct.Augmentors.SequentAugmentor
import org.keymaerax.infrastruct.Position
import spray.json.JsString

class GetFormulaPrettyStringRequest(db: DBAbstraction, userId: String, proofId: String, nodeId: String, pos: Position)
    extends UserProofRequest(db, userId, proofId) with ReadRequest {
  override protected def doResultingResponse(): Response = {
    DbProofTree(db, proofId).locate(nodeId).flatMap(_.goal.flatMap(_.sub(pos))) match {
      case None => new ErrorResponse("Unknown position " + pos + " at node " + nodeId)
      case Some(e: Expression) => new PlainResponse("prettyString" -> JsString(e.prettyString))
    }
  }
}
