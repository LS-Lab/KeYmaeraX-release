/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.models

import edu.cmu.cs.ls.keymaerax.hydra.{BooleanResponse, DBAbstraction, Response, UserRequest, WriteRequest}

import scala.collection.immutable.{List, Nil}

class DeleteAllModelsRequest(db: DBAbstraction, userId: String) extends UserRequest(userId, _ => true) with WriteRequest {
  override def resultingResponses(): List[Response] = {
    val allModels = db.getModelList(userId).map(_.modelId)
    allModels.foreach(db.deleteModel)
    BooleanResponse(flag = true) :: Nil
  }
}
