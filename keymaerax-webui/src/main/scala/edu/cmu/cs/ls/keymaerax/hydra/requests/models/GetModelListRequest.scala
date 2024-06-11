/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.models

import edu.cmu.cs.ls.keymaerax.hydra.responses.models.ModelListResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ReadRequest, Response, UserRequest}

class GetModelListRequest(db: DBAbstraction, userId: String, folder: Option[String])
    extends UserRequest(userId, _ => true) with ReadRequest {
  def resultingResponse(): Response = {
    // @todo folders in DB
    val allModels = db.getModelList(userId).filterNot(_.temporary)
    val models = folder match {
      case None => allModels
      case Some(f) => allModels.filter(_.name.startsWith(f + "/")).map(m => m.copy(name = m.name.stripPrefix(f + "/")))
    }
    new ModelListResponse(models)
  }
}
