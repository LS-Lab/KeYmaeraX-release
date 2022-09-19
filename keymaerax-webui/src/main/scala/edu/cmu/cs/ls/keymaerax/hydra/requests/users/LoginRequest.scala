/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.requests.users

import edu.cmu.cs.ls.keymaerax.hydra.responses.users.LoginResponse
import edu.cmu.cs.ls.keymaerax.hydra.{DBAbstraction, ErrorResponse, ReadRequest, Request, Response, SessionManager}

import scala.collection.immutable.{List, Nil}

class LoginRequest(db: DBAbstraction, userId: String, password: String) extends Request with ReadRequest {
  override def resultingResponses(): List[Response] = {
    val check = db.checkPassword(userId, password)
    db.getUser(userId) match {
      case Some(user) =>
        val sessionToken =
          if (check) Some(SessionManager.add(user))
          else None
        new LoginResponse(check, user, sessionToken) :: Nil
      case None => new ErrorResponse("Unable to login user " + userId
        + ". Please double-check user name and password, or register a new user.") :: Nil
    }
  }
}