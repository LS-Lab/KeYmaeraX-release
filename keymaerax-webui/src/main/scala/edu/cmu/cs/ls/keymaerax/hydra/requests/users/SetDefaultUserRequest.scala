/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.users

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.hydra.{
  BooleanResponse,
  DBAbstraction,
  ErrorResponse,
  LocalhostOnlyRequest,
  Response,
  WriteRequest,
}

import scala.collection.immutable.{List, Nil}

class SetDefaultUserRequest(db: DBAbstraction, userId: String, password: String, useDefault: Boolean)
    extends LocalhostOnlyRequest with WriteRequest {
  override def resultingResponses(): List[Response] = {
    if (useDefault) {
      if (db.checkPassword(userId, password)) {
        Configuration.set(Configuration.Keys.DEFAULT_USER, userId, saveToFile = true)
        Configuration.set(Configuration.Keys.USE_DEFAULT_USER, "true", saveToFile = true)
        BooleanResponse(flag = true) :: Nil
      } else new ErrorResponse("Failed to set default user") :: Nil
    } else {
      Configuration.remove(Configuration.Keys.DEFAULT_USER, saveToFile = true)
      Configuration.set(Configuration.Keys.USE_DEFAULT_USER, "false", saveToFile = true)
      BooleanResponse(flag = true) :: Nil
    }
  }
}
