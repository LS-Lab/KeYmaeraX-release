/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.users

import org.keymaerax.hydra.responses.users.LoginResponse
import org.keymaerax.hydra.{DBAbstraction, ErrorResponse, Request, Response, SessionManager, WriteRequest}

class CreateUserRequest(db: DBAbstraction, userId: String, password: String, mode: String)
    extends Request with WriteRequest {
  override def resultingResponse(): Response = {
    db.getUser(userId) match {
      case Some(user) => new LoginResponse(false, user, None)
      case None =>
        db.createUser(userId, password, mode)
        db.getUser(userId) match {
          case Some(newUser) => new LoginResponse(true, newUser, Some(SessionManager.add(newUser)))
          case None => new ErrorResponse("Failed to create user " + userId)
        }
    }
  }
}
