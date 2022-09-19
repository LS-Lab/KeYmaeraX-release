/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.proofs

import edu.cmu.cs.ls.keymaerax.hydra.responses.models.GetModelTacticResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ReadRequest, Response, UserRequest}

import scala.collection.immutable.{List, Nil}

class GetModelTacticRequest(db: DBAbstraction, userId: String, modelId: String) extends UserRequest(userId, _ => true) with ReadRequest {
  def resultingResponses(): List[Response] = new GetModelTacticResponse(db.getModel(modelId)) :: Nil
}
