package edu.cmu.cs.ls.keymaera.hydra

import akka.actor.Actor
import spray.routing._
import spray.http._
import MediaTypes._

class RestApiActor extends Actor with RestApi {
  def actorRefFactory = context

  //Note: separating the actor and router allows resting of the router without
  //spinning up an actor.
  def receive = runRoute(myRoute)
}

/**
 * RestApi is the API router. See REAMDE.md for a description of the API.
 */
trait RestApi extends HttpService {
  val javascriptRoute = pathPrefix("js") { get { getFromResourceDirectory("js") } }
  val cssRoute = pathPrefix("css") { get { getFromResourceDirectory("css") } }
  val staticRoute = pathPrefix("static") { get { getFromResourceDirectory("static") } }

  val startSession = path("startSession") {
    get {
      respondWithMediaType(`application/json`) {
        complete("{sessionName: \"newkey\"}") //TODO-nrf 
      }
    }
  }

  val requestUpdate = path("requestUpdate") {
    get {
      respondWithMediaType(`application/json`) {
        complete("[]")
      }
    }
  }

//  val nodeClosed = path("nodeClosed") undefCall
//  val nodePruned = path("nodePruned") undefCall
//  val limitExceeded = path("limitExceeded") undefCall
//  val startingStrategy = path("startingStrategy") undefCall
//  val applyTactic = path("applyTactic") undefCall
//  val getNode = path("getNode") undefCall

  val routes =
    javascriptRoute ::
    cssRoute ::
    staticRoute ::
    startSession ::
    requestUpdate ::
//    nodeClosed ::
//    nodePruned ::
//    limitExceeded ::
//    startingStrategy ::
//    applyTactic ::
//    getNode ::
    Nil

  val myRoute = routes.reduce(_ ~ _)
}
