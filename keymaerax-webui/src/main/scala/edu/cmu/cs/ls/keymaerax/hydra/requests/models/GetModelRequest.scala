/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.models

import edu.cmu.cs.ls.keymaerax.hydra.responses.models.GetModelResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ReadRequest, Response, UserRequest}

import scala.collection.immutable.{List, Nil}

class GetModelRequest(db: DBAbstraction, userId: String, modelId: String)
    extends UserRequest(userId, (id: String) => db.getModel(modelId).userId == id) with ReadRequest {
  def resultingResponses(): List[Response] = new GetModelResponse(db.getModel(modelId)) :: Nil
}
