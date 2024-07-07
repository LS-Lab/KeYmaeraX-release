/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.users

import org.keymaerax.Configuration
import org.keymaerax.hydra.{BooleanResponse, DBAbstraction, ErrorResponse, LocalhostOnlyRequest, Response, WriteRequest}

class SetDefaultUserRequest(db: DBAbstraction, userId: String, password: String, useDefault: Boolean)
    extends LocalhostOnlyRequest with WriteRequest {
  override def resultingResponse(): Response = {
    if (useDefault) {
      if (db.checkPassword(userId, password)) {
        Configuration.set(Configuration.Keys.DEFAULT_USER, userId, saveToFile = true)
        Configuration.set(Configuration.Keys.USE_DEFAULT_USER, "true", saveToFile = true)
        BooleanResponse(flag = true)
      } else new ErrorResponse("Failed to set default user")
    } else {
      Configuration.remove(Configuration.Keys.DEFAULT_USER, saveToFile = true)
      Configuration.set(Configuration.Keys.USE_DEFAULT_USER, "false", saveToFile = true)
      BooleanResponse(flag = true)
    }
  }
}
