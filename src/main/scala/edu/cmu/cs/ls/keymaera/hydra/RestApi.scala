package edu.cmu.cs.ls.keymaera.hydra

import akka.actor.Actor
import spray.routing._
import spray.http._
import MediaTypes._
import scala.collection.mutable.HashMap
import spray.json.JsArray

class RestApiActor extends Actor with RestApi {
  def actorRefFactory = context

  //Note: separating the actor and router allows testing of the router without
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
      val newKey = ServerState.createSession()
      respondWithMediaType(`application/json`) {
        complete("{\"sessionName\": \""+newKey+"\"}") //TODO-nrf 
      }
    }
  }

  val getUpdates = path("getUpdates") {
    get {
      respondWithMediaType(`application/json`) {
        parameter("sessionName") { 
           sessionName => complete(ServerState.getUpdates(sessionName))
        }
      }
    }
  }
  
  val startNewProblem = path("startNewProblem") {
    post {
      parameter("sessionName") { sessionName => {
        decompressRequest() {
          entity(as[String]) {
            problem => {
              val request = new Problem(sessionName, problem)
              val result = KeYmaeraClient.serviceRequest(sessionName, request) 
              complete("[]")
            }
          }
        }
      }}
    }
  }
  
  val formulaToString = path("formulaToString") {
    get {
      parameter("sessionName", "uid") { (sessionName,uid) => {
        val request = new FormulaToStringRequest(sessionName, uid)
        val result = KeYmaeraClient.serviceRequest(sessionName, request)
        complete("[" + result.map(_.json).mkString(",") + "]")
      }}
    }
  }
 
  val formulaToInteractiveString = path("formulaToInteractiveString") {
    get {
      parameter("sessionName", "uid") { (sessionName,uid) => {
        val request = new FormulaToInteractiveStringRequest(sessionName, uid)
        val result = KeYmaeraClient.serviceRequest(sessionName, request)
        complete("[" + result.map(_.json).mkString(",") + "]")
      }}
    }
  }
  
  val formulaFromUid = path("formulaFromUid") {
    get {
      parameter("sessionName", "uid") { (sessionName,uid) => {
        val request = new FormulaFromUidRequest(sessionName, uid)
        val result = KeYmaeraClient.serviceRequest(sessionName, request)
        complete("[" + result.map(_.json).mkString(",") + "]")
      }}
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
    //Real stuff begins here.
    getUpdates ::
    startSession ::
    startNewProblem ::
    formulaToString ::
    formulaToInteractiveString ::
    formulaFromUid::
    Nil

  val myRoute = routes.reduce(_ ~ _)
}
