/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.restapi

import akka.http.scaladsl.server.Directives._
import akka.http.scaladsl.server.Route
import org.keymaerax.hydra.RestApi.{completeRequest, completeResponse, database}
import org.keymaerax.hydra._
import org.keymaerax.hydra.requests.tools._
import org.keymaerax.parser.StringConverter._
import spray.json._

import scala.language.postfixOps

object Tools {

  val toolStatus: Route = path("tools" / "vitalSigns") {
    pathEnd {
      get {
        completeRequest(
          new ToolStatusRequest(database, org.keymaerax.Configuration(org.keymaerax.Configuration.Keys.QE_TOOL)),
          EmptyToken(),
        )
      }
    }
  }

  val cancelTool: Route =
    path("tools" / "cancel") { pathEnd { get { completeRequest(new CancelToolRequest(), EmptyToken()) } } }

  val restartTool: Route = path("tools" / "restart") {
    pathEnd {
      get {
        completeRequest(
          new RestartToolRequest(database, org.keymaerax.Configuration(org.keymaerax.Configuration.Keys.QE_TOOL)),
          EmptyToken(),
        )
      }
    }
  }

  val testToolConnection: Route = path("tools" / "testConnection") {
    pathEnd {
      get {
        completeRequest(
          new TestToolConnectionRequest(
            database,
            org.keymaerax.Configuration(org.keymaerax.Configuration.Keys.QE_TOOL),
          ),
          EmptyToken(),
        )
      }
    }
  }

  val setupSimulation: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "setupSimulation") { (userId, proofId, nodeId) =>
      {
        pathEnd {
          get {
            val request = new SetupSimulationRequest(database, userId, proofId, nodeId)
            completeRequest(request, t)
          }
        }
      }
    }

  val simulate: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "simulate") { (userId, proofId, nodeId) =>
      {
        pathEnd {
          post {
            entity(as[String]) { params =>
              {
                val obj = JsonParser(params).asJsObject()
                val initial = obj.fields("initial").asInstanceOf[JsString].value.asFormula
                val stateRelation = obj.fields("stateRelation").asInstanceOf[JsString].value.asFormula
                val numSteps = obj.fields("numSteps").asInstanceOf[JsNumber].value.intValue
                obj.fields("stepDuration").asInstanceOf[JsString].value.asTerm match {
                  case dt: org.keymaerax.core.Number =>
                    val request =
                      new SimulationRequest(database, userId, proofId, nodeId, initial, stateRelation, numSteps, 1, dt)
                    completeRequest(request, t)
                  case t => complete(completeResponse(new ErrorResponse(
                      "Expected a number as step duration, but got " + t.prettyString
                    )))
                }
              }
            }
          }
        }
      }
    }

  val odeConditions: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "odeConditions") { (userId, proofId, nodeId) =>
      {
        pathEnd {
          get {
            val request = new ODEConditionsRequest(database, userId, proofId, nodeId)
            completeRequest(request, t)
          }
        }
      }
    }

  val pegasusCandidates: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "pegasusCandidates") { (userId, proofId, nodeId) =>
      {
        pathEnd {
          get {
            val request = new PegasusCandidatesRequest(database, userId, proofId, nodeId)
            completeRequest(request, t)
          }
        }
      }
    }

  val counterExample: SessionToken => Route = (t: SessionToken) =>
    path("proofs" / "user" / Segment / Segment / Segment / "counterExample") { (userId, proofId, nodeId) =>
      {
        pathEnd {
          get {
            parameters(Symbol("assumptions").as[String], Symbol("fmlIndices").as[String]) {
              (assumptions: String, fmlIndices: String) =>
                val request = new CounterExampleRequest(database, userId, proofId, nodeId, assumptions, fmlIndices)
                completeRequest(request, t)
            }
          }
        }
      }
    }

}
