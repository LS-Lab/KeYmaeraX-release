/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.restapi

import akka.http.scaladsl.server.Route
import spray.json._
import akka.http.scaladsl.server.Directives._

import org.keymaerax.hydra.RestApi.{completeRequest, database, userPrefix}
import org.keymaerax.hydra._
import org.keymaerax.hydra.requests.modelplex._

import scala.annotation.tailrec
import scala.language.postfixOps

object ModelPlex {

  val modelplex: SessionToken => Route = (t: SessionToken) =>
    userPrefix { userId =>
      pathPrefix("model" / Segment / "modelplex" / "generate" / Segment / Segment / Segment / Segment) {
        (modelId, artifact, monitorKind, monitorShape, conditionKind) =>
          pathEnd {
            get {
              parameters(Symbol("vars").as[String] ?) { vars =>
                {
                  val theVars: List[String] = vars match {
                    case Some(v) =>
                      v.parseJson match { case a: JsArray => a.elements.map({ case JsString(s) => s }).toList }
                    case None => List.empty
                  }
                  val r = new ModelPlexRequest(
                    database,
                    userId,
                    modelId,
                    artifact,
                    monitorKind,
                    monitorShape,
                    conditionKind,
                    theVars,
                  )
                  completeRequest(r, t)
                }
              }
            }
          }
      }
    }

  val testSynthesis: SessionToken => Route = (t: SessionToken) =>
    userPrefix { userId =>
      pathPrefix("model" / Segment / "testcase" / "generate" / Segment / Segment / Segment) {
        (modelId, monitorKind, amount, timeout) =>
          pathEnd {
            get {
              parameters(Symbol("kinds").as[String] ?) { kinds =>
                {
                  val theKinds: Map[String, Boolean] = kinds match {
                    case Some(v) => v.parseJson.asJsObject.fields.map({ case (k, JsBoolean(v)) => k -> v })
                  }
                  val to = timeout match {
                    case "0" => None
                    case s => Some(Integer.parseInt(s))
                  }
                  val r = new TestSynthesisRequest(
                    database,
                    userId,
                    modelId,
                    monitorKind,
                    theKinds,
                    Integer.parseInt(amount),
                    to,
                  )
                  completeRequest(r, t)
                }
              }
            }
          }
      }
    }

}
