/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.users

import edu.cmu.cs.ls.keymaerax.hydra.responses.users.LoginResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ErrorResponse, Request, Response, SessionManager, WriteRequest}

import scala.collection.immutable.{List, Nil}

class CreateUserRequest(db: DBAbstraction, userId: String, password: String, mode: String) extends Request with WriteRequest {
  override def resultingResponses(): List[Response] = {
    db.getUser(userId) match {
      case Some(user) => new LoginResponse(false, user, None) ::  Nil
      case None =>
        db.createUser(userId, password, mode)
        db.getUser(userId) match {
          case Some(newUser) => new LoginResponse(true, newUser, Some(SessionManager.add(newUser))) ::  Nil
          case None => new ErrorResponse("Failed to create user " + userId) :: Nil
        }
    }
  }
}
