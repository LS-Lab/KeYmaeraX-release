/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.restapi

import akka.http.scaladsl.server.Route
import spray.json._
import akka.http.scaladsl.server.Directives._
import edu.cmu.cs.ls.keymaerax.hydra.RestApi.{completeRequest, database}
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.hydra.requests.configuration.{GetUserThemeRequest, SetUserThemeRequest}
import edu.cmu.cs.ls.keymaerax.hydra.requests.users._

import scala.language.postfixOps

object Users {

  val users: Route = pathPrefix("user" / Segment / Segment / "mode" / Segment) { (username, password, mode) =>
    {
      pathEnd {
        get {
          val request = new LoginRequest(database, username, password)
          completeRequest(request, EmptyToken())
        } ~ post {
          val request = new CreateUserRequest(database, username, password, mode)
          completeRequest(request, EmptyToken())
        }
      }
    }
  }

  val defaultLogin: Route = pathPrefix("user" / Segment / Segment / "defaultLogin") { (username, password) =>
    {
      pathEnd {
        get {
          val request = new LocalLoginRequest(database, username, password)
          completeRequest(request, EmptyToken())
        }
      }
    }
  }

  val setDefaultUser: Route =
    pathPrefix("user" / Segment / Segment / "setDefaultUser" / Segment) { (username, password, useDefault) =>
      {
        pathEnd {
          post {
            val request = new SetDefaultUserRequest(database, username, password, useDefault == "true")
            completeRequest(request, EmptyToken())
          }
        }
      }
    }

  val logoff: SessionToken => Route = (t: SessionToken) =>
    path("user" / "logoff") {
      pathEnd {
        get {
          t match {
            case ut: UserToken =>
              SessionManager.defaultUserTokenKey = None
              SessionManager.remove(ut.token)
            case NewlyExpiredToken(_) => // Well, that was convienant.
            case _ => // that works too.
          }
          complete("[]")
        }
      }
    }

  val userTheme: SessionToken => Route = (t: SessionToken) =>
    path("users" / Segment / "theme") { userId =>
      pathEnd {
        get {
          val request = new GetUserThemeRequest(database, userId)
          completeRequest(request, t)
        } ~ post {
          entity(as[String]) { themeStr =>
            {
              def convert(k: String, v: JsValue): (String, String) = k match {
                case "renderMargins" => v match {
                    case _: JsArray => k -> v.toString()
                    case o: JsObject if Set("0", "1").subsetOf(o.fields.keySet) =>
                      k -> JsArray(o.fields("0"), o.fields("1")).toString
                    case _ => throw new IllegalArgumentException(
                        "Render margins must be either an array of numbers or an object {'0': JsNumber, '1': JsNumber}, but got " +
                          v.toString
                      )
                  }
                case _ => k -> v.toString()
              }

              val theme = themeStr.parseJson.asJsObject.fields.map({ case (k, v) => convert(k, v) })
              val request =
                new SetUserThemeRequest(database, userId, theme("css"), theme("fontSize"), theme("renderMargins"))
              completeRequest(request, t)
            }
          }
        }
      }
    }

}
