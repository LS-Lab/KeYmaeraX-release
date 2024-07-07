/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.models

import org.keymaerax.hydra.{DBAbstraction, DatabasePopulator, HtmlResponse, ReadRequest, Request, Response}

import java.io.{PrintWriter, StringWriter}
import java.net.URLEncoder

class OpenGuestArchiveRequest(db: DBAbstraction, uri: String, archiveName: String) extends Request with ReadRequest {
  override def resultingResponse(): Response = {
    try {
      val userId = uri
      val sanitizedUserId = URLEncoder.encode(uri, "UTF-8")
      val pwd = "guest"
      val userExists = db.userExists(userId)
      if (!userExists) db.createUser(userId, pwd, "3")

      val models = db.getModelList(userId)
      DatabasePopulator.importKya(db, userId, uri, models)

      // @todo template engine, e.g., twirl, or at least figure out how to parse from a string
      val html = {
        <html lang="en" ng-app="loginApp" ng-controller="ServerInfoCtrl">
          <head>
            <meta charset="utf-8"/>
            <meta http-equiv="X-UA-Compatible" content="IE=edge"/>
            <meta name="viewport" content="width=device-width, initial-scale=1"/>
            <meta name="description" content=""/>
            <meta name="author" content="Logical Systems Lab, Carnegie Mellon University"/>
            <link rel="icon" href="../../favicon.ico"/>
            <title>KeYmaera X</title>
            <link href="/css/bootstrap.css" rel="stylesheet" type="text/css"/>
            <link href="/css/font-awesome.min.css" rel="stylesheet" type="text/css"/>
            <link href="/css/sticky-footer-navbar.css" rel="stylesheet"/>
          </head>
          <body>
            <script src="/js/jquery.min.js"></script>
            <script src="/js/jquery-ui.min.js"></script>
            <script src="/js/bootstrap/bootstrap.min.js"></script>
            <script src="/js/angular/angular.min.js"></script>
            <script src="/js/angular/angular-sanitize.min.js"></script>
            <script src="/js/angular/angular-cookies.min.js"></script>
            <script src="/js/angular/angular-route.min.js"></script>
            <script src="/js/angular/angular-animate.min.js"></script>
            <script src="/js/angular/bootstrap/ui-bootstrap-tpls-2.5.0.min.js"></script>
            <script src="/js/loginApp.js"></script>
            <script src="/js/services/services.js"></script>
            <script src="/js/services/session.js"></script>
            <script src="/js/controllers/interceptors.js"></script>
            <script src="/js/controllers/auth.js"></script>
            <script src="/js/controllers.js"></script>
            <script src="/js/controllers/factories.js"></script>
            <script src="/js/controllers/errorReport.js"></script>
            <script src="/js/controllers/login.js"></script>
            <script src="/js/controllers/serverinfo.js"></script>

            <div ng-controller="LoginCtrl" ng-init={"login('" + sanitizedUserId + "','" + pwd + "',true);"}></div>
          </body>
        </html>
      }
      HtmlResponse(html)
    } catch {
      // Return a user-friendly message, since there's no user interface running yet to render a JSON error response
      case ex: Throwable =>
        val stacktrace = {
          val sw = new StringWriter
          ex.printStackTrace(new PrintWriter(sw))
          sw.toString
        }
        val html = {
          <html lang="en" ng-app="loginApp" ng-controller="ServerInfoCtrl">
            <head>
              <meta charset="utf-8"/>
              <meta http-equiv="X-UA-Compatible" content="IE=edge"/>
              <meta name="viewport" content="width=device-width, initial-scale=1"/>
              <meta name="description" content=""/>
              <meta name="author" content="Logical Systems Lab, Carnegie Mellon University"/>
              <link rel="icon" href="../../favicon.ico"/>
              <title>KeYmaera X</title>
              <link href="/css/bootstrap.css" rel="stylesheet" type="text/css"/>
              <link href="/css/font-awesome.min.css" rel="stylesheet" type="text/css"/>
              <link href="/css/sticky-footer-navbar.css" rel="stylesheet"/>
            </head>
            <body>
              <h1>Error browsing archive</h1>
              <p>Please double-check the archive path/name</p>
              <p>Archive location:
                {archiveName}
              </p>
              <p>Archive remote location:
                {uri}
              </p>
              <h3>Error details</h3>
              <p>
                {stacktrace}
              </p>
            </body>
          </html>
        }
        HtmlResponse(html)
    }
  }
}
