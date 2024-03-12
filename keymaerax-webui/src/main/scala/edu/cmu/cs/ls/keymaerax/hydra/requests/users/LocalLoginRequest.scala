/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.users

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.hydra.responses.users.{DefaultLoginResponse, LoginResponse}
import edu.cmu.cs.ls.keymaerax.hydra.{
  DBAbstraction,
  ErrorResponse,
  LocalhostOnlyRequest,
  ReadRequest,
  Response,
  SessionManager,
}

import scala.collection.immutable.{List, Nil}

class LocalLoginRequest(db: DBAbstraction, userId: String, password: String)
    extends LocalhostOnlyRequest with ReadRequest {
  override def resultingResponses(): List[Response] = {
    if (Configuration.getString(Configuration.Keys.USE_DEFAULT_USER).contains("true") && userId == "local") {
      Configuration.getString(Configuration.Keys.DEFAULT_USER) match {
        case Some(userId) => db.getUser(userId) match {
            case Some(user) =>
              val sessionToken = Some(SessionManager.add(user))
              new LoginResponse(true, user, sessionToken) :: Nil
            case None => DefaultLoginResponse(triggerRegistration = true) :: Nil
          }
        case None => DefaultLoginResponse(triggerRegistration = true) :: Nil
      }
    } else {
      val check = db.checkPassword(userId, password)
      db.getUser(userId) match {
        case Some(user) =>
          val sessionToken = if (check) Some(SessionManager.add(user)) else None
          new LoginResponse(check, user, sessionToken) :: Nil
        case None =>
          new ErrorResponse(
            "Unable to login user " + userId + ". Please double-check user name and password, or register a new user."
          ) :: Nil
      }
    }
  }
}
