/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.{BooleanResponse, DBAbstraction, Response, UserRequest, WriteRequest}

import scala.collection.immutable.{List, Nil}

class AddModelTacticRequest(db: DBAbstraction, userId: String, modelId: String, tactic: String) extends UserRequest(userId, _ => true) with WriteRequest {
  def resultingResponses(): List[Response] = {
    val tacticId = db.addModelTactic(modelId, tactic)
    BooleanResponse(tacticId.isDefined) :: Nil
  }
}
