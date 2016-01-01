/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.hydra

import _root_.edu.cmu.cs.ls.keymaerax.btacticinterface.BTacticParser
import edu.cmu.cs.ls.keymaerax.btactics.{Find, Fixed, DerivationInfo}
import _root_.edu.cmu.cs.ls.keymaerax.hydra.SQLite.SQLiteDB
import _root_.edu.cmu.cs.ls.keymaerax.tactics.{AntePosition, SuccPosition, Position, PosInExpr}
import akka.actor.Actor
import spray.routing._
import spray.http._
import spray.json._

class RestApiActor extends Actor with RestApi {
  def actorRefFactory = context

  //Note: separating the actor and router allows testing of the router without
  //spinning up an actor.
  def receive = runRoute(myRoute)
}

/**
 * RestApi is the API router. See README.md for a description of the API.
 */
trait RestApi extends HttpService {
  val database = DBAbstractionObj.defaultDatabase //SQLite //Not sure when or where to create this... (should be part of Boot?)

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Helper Methods
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  private def getUserFromUserIdCookieContent(userIdContent : String):String = userIdContent //for now...

  private def getFileContentsFromFormData(item : BodyPart) : String = {
    val entity = item.entity
    val headers = item.headers
    val content = item.entity.data.asString

    //Just FYI here's how you get the content type...
    val contentType = headers.find(h => h.is("content-type")).get.value

    content
  }

  private def getFileNameFromFormData(item:BodyPart) : String = {
    item.headers.find(h => h.is("content-disposition")).get.value.split("filename=").last
  }

  private def standardCompletion(r : Request) : String = {
    val responses = r.getResultingResponses()
    responses match {
      case hd :: Nil => hd.getJson.prettyPrint
      case _         =>
        responses.foldLeft("[")( (prefix, response) => prefix + "," + response.getJson.prettyPrint) + "]"
    }
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Begin Routing
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //Some common partials.
  val userPrefix = pathPrefix("user" / Segment)

  //The static directory.
  val staticRoute = pathPrefix("") { get { getFromResourceDirectory("") } }
  val homePage = path("") { get {getFromResource("index_bootstrap.html")}}


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Users
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  val users = pathPrefix("user" / Segment / Segment) { (username, password) => {
    pathEnd {
      get {
        val request = new LoginRequest(database,username,password)
        complete(request.getResultingResponses().last.getJson.prettyPrint)
      } ~
      post {
        val request = new CreateUserRequest(database, username, password)
        complete(request.getResultingResponses().last.json.prettyPrint)
      }
    }
  }}

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Models
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // FYI to get cookies do this:
  val cookieecho = pathPrefix("cookie_echo") { cookie("userId") { userId => {
    complete(userId.content)
  }}}

  // GET /models/user returns a list of all models belonging to this user. The cookie must be set.
  val modelList = pathPrefix("models" / "users" / Segment) {userId => { pathEnd { get {
    val request = new GetModelListRequest(database, userId)
    val responses = request.getResultingResponses()
    if(responses.length != 1) throw new Exception("Should only have a single response.")
    complete(responses.last.json.prettyPrint)
  }}}}

  //POST /users/<user id>/model/< name >/< keyFile >
  val userModel = userPrefix {userId => {pathPrefix("model" / Segment) {modelNameOrId => {pathEnd {
    post {
      entity(as[MultipartFormData]) { formData => {
        if(formData.fields.length > 1) ??? //should only have a single file.
        val data = formData.fields.last
        val contents = getFileContentsFromFormData(data)
        val request = new CreateModelRequest(database, userId, modelNameOrId, contents)
        complete(standardCompletion(request))
      }}
    } ~
    get {
      val request = new GetModelRequest(database, userId, modelNameOrId)
      complete(standardCompletion(request))
    }
  }}}}}

  //Because apparently FTP > modern web.
  val userModel2 = userPrefix {userId => {pathPrefix("modeltextupload" / Segment) {modelNameOrId =>
  {pathEnd {
    post {
      entity(as[String]) { contents => {
        val request = new CreateModelRequest(database, userId, modelNameOrId, contents)
        complete(standardCompletion(request))
      }}}}}}}}

  val modelTactic = path("user" / Segment / "model" / Segment / "tactic") { (userId, modelId) => pathEnd {
    get {
      val request = new GetModelTacticRequest(database, userId, modelId)
      complete(standardCompletion(request))
    }
  }}

  val runModelTactic = path("user" / Segment / "model" / Segment / "tactic" / "run") { (userId, modelId) => pathEnd {
    post {
      val request = new RunModelInitializationTacticRequest(database, userId, modelId)
      complete(standardCompletion(request))
    }
  }}

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Proofs
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  val createProof = path("models" / "users" / Segment / "model" / Segment / "createProof") { (userId, modelId) => { pathEnd {
    post {
      entity(as[String]) { x => {
        val obj = x.parseJson
        val proofName        = obj.asJsObject.getFields("proofName").last.asInstanceOf[JsString].value
        val proofDescription = obj.asJsObject.getFields("proofDescription").last.asInstanceOf[JsString].value
        val request = new CreateProofRequest(database, userId, modelId, proofName, proofDescription)
        complete(standardCompletion(request))
      }}
    }
  }}}

  val proofListForModel = path("models" / "users" / Segment / "model" / Segment / "proofs") { (userId, modelId) => { pathEnd {
    get {
      val request = new ProofsForModelRequest(database, modelId)
      complete(standardCompletion(request))
    }
  }}}

  val proofList = path("models" / "users" / Segment / "proofs") { (userId) => { pathEnd {
    get {
      val request = new ProofsForUserRequest(database, userId)
      complete(standardCompletion(request))
    }
  }}}

  val openProof = path("proofs" / "user" / Segment / Segment) { (userId, proofId) => { pathEnd {
    get {
      val request = new OpenProofRequest(database, userId, proofId)
      complete(standardCompletion(request))
    }
  }}}

  val dashInfo = path("users" / Segment / "dashinfo") { userId => pathEnd {
    get {
      val request = new DashInfoRequest(database, userId)
      complete(standardCompletion(request))
    }
  }}


  val proofTasks = path("proofs" / "user" / Segment / Segment / "agenda") { (userId, proofId) => { pathEnd {
    get {
      val request = new GetProofAgendaRequest(database, userId, proofId)
      complete(standardCompletion(request))
    }
  }}}

  val proofTasksNew = path("proofs" / "user" / Segment / Segment / "agendaawesome") { (userId, proofId) => { pathEnd {
    get {
      val request = new GetAgendaAwesomeRequest(database, userId, proofId)
      complete(standardCompletion(request))
    }
  }}}

  val proofTasksParent = path("proofs" / "user" / Segment / Segment / Segment / Segment / "parent") { (userId, proofId, nodeId, goalId) => { pathEnd {
    get {
      val request = new ProofTaskParentRequest(database, userId, proofId, nodeId, goalId)
      complete(standardCompletion(request))
    }
  }}}

  val proofTasksPathAll = path("proofs" / "user" / Segment / Segment / Segment / Segment / "pathall") { (userId, proofId, nodeId, goalId) => { pathEnd {
    get {
      val request = new GetPathAllRequest(database, userId, proofId, nodeId, goalId)
      complete(standardCompletion(request))
    }
  }}}

  val proofTasksBranchRoot = path("proofs" / "user" / Segment / Segment / Segment / Segment / "branchroot") { (userId, proofId, nodeId, goalId) => { pathEnd {
    get {
      val request = new GetBranchRootRequest(database, userId, proofId, nodeId, goalId)
      complete(standardCompletion(request))
    }
  }}}

  /* Strictly positive position = SuccPosition, strictly negative = AntePosition, 0 not used */
  def parseFormulaId(id:String):Position = {
    val (idx :: inExprs) = id.split(',').toList.map({case str => str.toInt})
    if(idx > 0) {
      new SuccPosition(idx-1, new PosInExpr(inExprs))
    } else if (idx < 0) {
      new AntePosition((-idx)-1)
    } else {
      throw new Exception("Invalid formulaId " + id + " in axiomList")
    }
  }

  val axiomList = path("proofs" / "user" / Segment / Segment / Segment / Segment / Segment / "list") { (userId, proofId, nodeId, goalId, formulaId) => { pathEnd {
    get {
      val request = new GetApplicableAxiomsRequest(database, userId, proofId, nodeId, goalId, parseFormulaId(formulaId))
      //@note mock data for right-clicking formulas
//      val request = formulaId match {
//        case "F5s0" => new MockRequest("/mockdata/andaxiomlist.json")
//        case "F5s1" => new MockRequest("/mockdata/ltaxiomlist.json")
//        case "1," => new MockRequest("/mockdata/implyaxiomlist.json")
//        case "1,1" => new MockRequest("/mockdata/loopaxiomlist.json")
//      }
      complete(standardCompletion(request))
    }
  }}}

  val doAt = path("proofs" / "user" / Segment / Segment / Segment / Segment / Segment / "doAt" / Segment) { (userId, proofId, nodeId, goalId, formulaId, tacticId) => { pathEnd {
    get {
      val request = new RunBelleTermRequest(database, userId, proofId, goalId, tacticId, Some(Fixed(parseFormulaId(formulaId))))
      complete(standardCompletion(request))
    }}
  }}

  val doInputAt = path("proofs" / "user" / Segment / Segment / Segment / Segment / Segment / "doInputAt" / Segment) { (userId, proofId, nodeId, goalId, formulaId, tacticId) => { pathEnd {
    post {
      entity(as[String]) { params => {
        val request = formulaId match {
          case "1,1" =>
            val input = JsonParser(params) // do something useful with the tactic input
            new MockRequest("/mockdata/loopresult.json")
        }
        complete(standardCompletion(request))
      }
    }}
  }}}

  val doExhaustive = path("proofs" / "user" / Segment / Segment / Segment / "doExhaustive" / Segment) { (userId, proofId, goalId, tacticId) => { pathEnd {
    get {
      val request = new RunBelleTermRequest(database, userId, proofId, goalId, tacticId, None)
      complete(standardCompletion(request))
    }}
  }}

  val doSearchRight = path("proofs" / "user" / Segment / Segment / Segment / "doSearchR" / Segment) { (userId, proofId, goalId, tacticId) => { pathEnd {
    get {
      val request = new RunBelleTermRequest(database, userId, proofId, goalId, tacticId, Some(Find(0, None, SuccPosition(0))))
      complete(standardCompletion(request))
    }}
  }}

  val doSearchLeft = path("proofs" / "user" / Segment / Segment / Segment / "doSearchL" / Segment) { (userId, proofId, goalId, tacticId) => { pathEnd {
    get {
      val request = new RunBelleTermRequest(database, userId, proofId, goalId, tacticId, Some(Find(0, None, AntePosition(0))))
      complete(standardCompletion(request))
    }}
  }}

  val pruneBelow = path("proofs" / "user" / Segment / Segment / Segment / Segment / "pruneBelow") { (userId, proofId, nodeId, goalId) => { pathEnd {
    get {
      val request = new PruneBelowRequest(database, userId, proofId, nodeId, goalId)
      complete(standardCompletion(request))
    }
  }}}

  val proofTask = path("proofs" / "user" / Segment / Segment / "agendaDetails" / Segment.?) { (userId, proofId, nodeId) => { pathEnd {
    get {
      val request = new GetProofNodeInfoRequest(database, userId, proofId, nodeId)
      complete(standardCompletion(request))
    }
  }}}

  val proofLoadStatus = path("proofs" / "user" / Segment / Segment / "status") { (userId, proofId) => { pathEnd {
    get {
      val request = new GetProofLoadStatusRequest(database, userId, proofId)
      complete(standardCompletion(request))
    }
  }}}

  val proofProgressStatus = path("proofs" / "user" / Segment / Segment / "progress") { (userId, proofId) => { pathEnd {
    get {
      val request = new GetProofProgressStatusRequest(database, userId, proofId)
      complete(standardCompletion(request))
    }
  }}}

  val proofCheckIsProved = path("proofs" / "user" / Segment / Segment / "validatedStatus") { (userId, proofId) => { pathEnd {
    get {
      val request = new CheckIsProvedRequest(database, userId, proofId)
      complete(standardCompletion(request))
    }
  }}}

  val nodeFormulaTactics = path("proofs" / "user" / Segment / Segment / "nodes" / Segment / "formulas" / Segment / "tactics") { (userId, proofId, nodeId, formulaId) => { pathEnd {
    get {
      val nId = if (proofId.equals(nodeId)) None else Some(nodeId)
      val fId = if (formulaId.equals("sequent")) None else Some(formulaId)
      val request = new GetApplicableTacticsRequest(database, userId, proofId, nId, fId)
      complete(standardCompletion(request))
    }
  }}}

  val nodeRunTactics = path("proofs" / "user" / Segment / Segment / "nodes" / Segment / "formulas" / Segment / "tactics" / "run" / Segment) { (userId, proofId, nodeId, formulaId, tacticId) => { pathEnd {
    post {
      entity(as[String]) { params => {
        val p = JsonParser(params).asJsObject.fields.map(param => param._1.toInt -> param._2.asInstanceOf[JsString].value)
        val nId = if (proofId.equals(nodeId)) None else Some(nodeId)
        val fId = if (formulaId.equals("sequent")) None else Some(formulaId)
        val request = new RunTacticRequest(database, userId, proofId, nId, fId, tacticId, p)
        complete(standardCompletion(request))
      }
      }
    }
  }}}

  val counterExample = path("proofs" / "user" / Segment / Segment / "nodes" / Segment / "counterExample") { (userId, proofId, nodeId) => {
    pathEnd {
      get {
        val request = new CounterExampleRequest(database, userId, proofId, nodeId)
        complete(standardCompletion(request))
      }
    }}
  }

  val kyxConfig = path("kyxConfig") {
    pathEnd {
      get {
        val request = new KyxConfigRequest(database)
        complete(standardCompletion(request))
      }
    }
  }

  val keymaeraXVersion = path("keymaeraXVersion") {
    pathEnd {
      get {
        val request = new KeymaeraXVersionRequest()
        complete(standardCompletion(request))
      }
    }
  }

  val mathematicaConfigSuggestion = path("config" / "mathematica" / "suggest") {
    pathEnd {
      get {
        val request = new GetMathematicaConfigSuggestionRequest(database)
        complete(standardCompletion(request))
      }
    }
  }

  val mathematicaConfig = path("config" / "mathematica") {
    pathEnd {
      get {
          val request = new GetMathematicaConfigurationRequest(database)
          complete(standardCompletion(request))
      } ~
      post {
        entity(as[String]) { params => {
          val p = JsonParser(params).asJsObject.fields.map(param => param._1.toString -> param._2.asInstanceOf[JsString].value)
          assert(p.contains("linkName"), "linkName not in: " + p.keys.toString())
          assert(p.contains("jlinkLibDir"), "jlinkLibDir not in: " + p.keys.toString()) //@todo These are schema violations and should be checked as such, but I needed to disable the validator.
          val linkName : String = p("linkName")
          val jlinkLibDir : String = p("jlinkLibDir")
          val request = new ConfigureMathematicaRequest(database, linkName, jlinkLibDir)
          complete(standardCompletion(request))
        }}
      }
    }
  }

  val mathematicaStatus = path("config" / "mathematicaStatus") {
    pathEnd {
      get {
        complete(standardCompletion(new MathematicaStatusRequest(database)))
      }
    }
  }

  val runClTerm = path("proofs" / "user" / Segment / Segment / "nodes" / Segment / "tactics" / "runTerm") { (userId, proofId, nodeId) => { pathEnd {
    post {
      entity(as[String]) { params => {
        val clTerm = JsonParser(params).asJsObject.fields.last._2.asInstanceOf[JsString].value
        val request = new RunCLTermRequest(database, userId, proofId, Some(nodeId), clTerm)
        complete(standardCompletion(request))
      }}
    }
  }}}

  val runBelleTerm = path("proofs" / "user" / Segment / Segment / "nodes" / Segment / "tactics" / "runBelleTerm") { (userId, proofId, nodeId) => { pathEnd {
    post {
      entity(as[String]) { params => {
        val term = JsonParser(params).asJsObject.fields.last._2.asInstanceOf[JsString].value
        val request = new RunBelleTermRequest(database, userId, proofId, nodeId, term, None)
        complete(standardCompletion(request))
  }}}}}}

  val changeProofName = path("proofs" / "user" / Segment / Segment / "name" / Segment) { (userId, proofId, newName) => { pathEnd {
    post {
      entity(as[String]) { params => {
        complete(standardCompletion(new UpdateProofNameRequest(database, proofId, newName)))
      }}
    }
  }}}

  val nodeSaturateTactics = path("proofs" / "user" / Segment / Segment / "nodes" / Segment / "formulas" / Segment / "tactics" / "run" / Segment / Segment) { (userId, proofId, nodeId, formulaId, tacticId, automation) => { pathEnd {
    post {
      entity(as[String]) { params => {
        val p = JsonParser(params).asJsObject.fields.map(param => param._1.toInt -> param._2.asInstanceOf[JsString].value)
        val nId = if (proofId.equals(nodeId)) None else Some(nodeId)
        val fId = if (formulaId.equals("sequent")) None else Some(formulaId)
        val request = new RunTacticRequest(database, userId, proofId, nId, fId, tacticId, p, Some(automation))
        complete(standardCompletion(request))
      }
      }
    }
  }}}

  val nodeRunTacticsByName = path("proofs" / "user" / Segment / Segment / "nodes" / Segment / "formulas" / Segment / "tactics" / "runByName" / Segment) { (userId, proofId, nodeId, formulaId, tacticName) => { pathEnd {
    post {
      entity(as[String]) { params =>
        val p = params match {
          case s : String if !s.isEmpty => JsonParser (params).asJsObject.fields.map (param => param._1.toInt -> param._2.asInstanceOf[JsString].value)
          case _ => Map.empty[Int,String]
        }
        val nId = if (proofId.equals(nodeId)) None else Some(nodeId)
        val fId = if (formulaId.equals("sequent")) None else Some(formulaId)
        val request = new RunTacticByNameRequest(database, userId, proofId, nId, fId, tacticName, p)
        complete(standardCompletion(request))
      }
    }
  }}}

  val nodeSaturateTacticsByName = path("proofs" / "user" / Segment / Segment / "nodes" / Segment / "formulas" / Segment / "tactics" / "runByName" / Segment / Segment) { (userId, proofId, nodeId, formulaId, tacticName, automation) => { pathEnd {
    post {
      entity(as[String]) { params =>
        val p = params match {
          case s : String if !s.isEmpty => JsonParser (params).asJsObject.fields.map (param => param._1.toInt -> param._2.asInstanceOf[JsString].value)
          case _ => Map.empty[Int,String]
        }
        val nId = if (proofId.equals(nodeId)) None else Some(nodeId)
        val fId = if (formulaId.equals("sequent")) None else Some(formulaId)
        val request = new RunTacticByNameRequest(database, userId, proofId, nId, fId, tacticName, p, Some(automation))
        complete(standardCompletion(request))
      }
    }
  }}}

  val dispatchedTactic = path("proofs" / "user" / Segment / Segment / "dispatchedTactics" / Segment) { (userId, proofId, tacticInstId) => { pathEnd {
    get {
      val request = new GetDispatchedTacticRequest(database, userId, proofId, tacticInstId)
      complete(standardCompletion(request))
    }
  }}}

  val dispatchedTerm = path("proofs" / "user" / Segment / Segment / "dispatchedTerm" / Segment) { (userId, proofId, termId) => { pathEnd {
    get {
      val request = new GetDispatchedTermRequest(database, userId, proofId, termId)
      complete(standardCompletion(request))
    }
  }}}

  /**
   * exactly like getting a proof tree except we get only the node instead of everything under it as well.
   */
  val sequent = path("proofs" / Segment / "sequent" / Segment.?) { (proofId, sequentId) => {
    get {
      val request = new GetNodeRequest(database, proofId, sequentId)
      complete(standardCompletion(request))
    }
  }}

  // proofs/user/< userid >/< proofid >/tree/< proofnodeid >
  val proofTree = path("proofs" / "user" / Segment / Segment / "tree" / Segment.?) { (userId, proofId, nodeId) => {
    get {
      val request = new GetProofTreeRequest(database, userId, proofId, nodeId)
      complete(standardCompletion(request))
    }
  }}

  val proofHistory = path("proofs" / "user" / Segment / Segment / "proofhistory") { (userId, proofId) => {
    get {
      val request = new GetProofHistoryRequest(database, userId, proofId)
      complete(standardCompletion(request))
    }
  }}

  val devAction = path("dev" / Segment) { (action) => {
    get {
      if(action.equals("deletedb")) {
        database.cleanup()
        complete("{}")
      }
      else {
        complete("{}")
      }
    }
  }}

  val isLocal = path("isLocal") { pathEnd { get {
    complete(standardCompletion(new IsLocalInstanceRequest()))
  }}}

  val shutdown = path("shutdown") { pathEnd { get {
    complete(standardCompletion(new ShutdownReqeuest()))
  }}}

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Licensing
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  val license = path("licenseacceptance") {  {
    get {
      complete(standardCompletion(new IsLicenseAcceptedRequest(database)))
    } ~
    post {
      complete(standardCompletion(new AcceptLicenseRequest(database)))
    }
  }}


  val initializeModel = path("models" / "users" / Segment / "model" / Segment / "initialize") { (userId, modelId) => pathEnd {
    post {
      complete(standardCompletion(new RunModelInitializationTacticRequest(database, userId, modelId)))
    }
  }}

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Route precedence
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  val routes =
    staticRoute           ::
    homePage              ::
    users                 ::
    modelList             ::
    modelTactic           ::
    userModel             ::
    userModel2            ::
    cookieecho            ::
    runModelTactic        ::
    createProof           ::
    proofListForModel     ::
    proofList             ::
    openProof             ::
    proofLoadStatus       ::
    changeProofName       ::
    proofProgressStatus   ::
    proofCheckIsProved    ::
    proofTasksNew         ::
    proofTasksParent      ::
    proofTasksPathAll     ::
    proofTasksBranchRoot  ::
    axiomList             ::
    doAt                  ::
    doInputAt             ::
    doExhaustive          ::
    doSearchLeft          ::
    doSearchRight         ::
    pruneBelow            ::
    proofTask             ::
    nodeFormulaTactics    ::
    nodeRunTactics        ::
    runClTerm             ::
    nodeSaturateTactics   ::
    nodeRunTacticsByName  ::
    nodeSaturateTacticsByName ::
    dispatchedTactic      ::
    dispatchedTerm        ::
    proofTree             ::
    proofHistory          ::
    devAction             ::
    sequent               ::
    dashInfo              ::
    counterExample        ::
    kyxConfig             ::
    keymaeraXVersion      ::
    mathematicaConfig     ::
    mathematicaStatus     ::
    mathematicaConfigSuggestion ::
    license ::
      initializeModel :: isLocal :: shutdown ::
    Nil
  val myRoute = routes.reduce(_ ~ _)

}
//
//
///// Leaving the implementation of the old api for reference.
//// Note that it's not clear when/if we need respondWithMediaType(`application/json`) ?
////
////  val startSession = path("startSession") {
////    get {
////      val newKey = ServerState.createSession()
////      respondWithMediaType(`application/json`) {
////        complete("{\"sessionName\": \""+newKey+"\"}") //TODO-nrf
////      }
////    }
////  }
////
////  /**
////   * TODO ew. See comment on ServerState.getUpdates...
////   */
////  val getUpdates = path("getUpdates") {
////    get {
////      respondWithMediaType(`application/json`) {
////        parameter("sessionName", "count") {
////           (sessionName, count) => complete(ServerState.getUpdates(sessionName, count))
////        }
////      }
////    }
////  }
////
////  val startNewProblem = path("startNewProblem") {
////    post {
////      parameter("sessionName") { sessionName => {
////        decompressRequest() {
////          entity(as[String]) {
////            problem => {
////              val request = new Problem(sessionName, problem)
////              val result = KeYmaeraClient.serviceRequest(sessionName, request)
////              complete("[]")
////            }
////          }
////        }
////      }}
////    }
////  }
////
////  val formulaToString = path("formulaToString") {
////    get {
////      parameter("sessionName", "uid") { (sessionName,uid) => {
////        val request = new FormulaToStringRequest(sessionName, uid)
////        val result = KeYmaeraClient.serviceRequest(sessionName, request)
////        complete("[" + result.map(_.json).mkString(",") + "]")
////      }}
////    }
////  }
////
////  val formulaToInteractiveString = path("formulaToInteractiveString") {
////    get {
////      parameter("sessionName", "uid") { (sessionName,uid) => {
////        val request = new FormulaToInteractiveStringRequest(sessionName, uid)
////        val result = KeYmaeraClient.serviceRequest(sessionName, request)
////        complete("[" + result.map(_.json).mkString(",") + "]")
////      }}
////    }
////  }
////
////  val formulaFromUid = path("formulaFromUid") {
////    get {
////      parameter("sessionName", "uid") { (sessionName,uid) => {
////        val request = new FormulaFromUidRequest(sessionName, uid)
////        val result = KeYmaeraClient.serviceRequest(sessionName, request)
////        complete("[" + result.map(_.json).mkString(",") + "]")
////      }}
////    }
////  }
////
////  val runTactic = path("runTactic") {
////    get {
////      parameter("sessionName", "tacticName", "uid", "parentId") {
////        (sessionName, tacticName, uid, parentId) => {
////          val request = RunTacticRequest(sessionName, tacticName, uid, None, parentId)
////          val result = KeYmaeraClient.serviceRequest(sessionName, request)
////          complete("[" + result.map(_.json).mkString(",") + "]")
////        }
////      }
////    }
////  }
////
////
////  //TODO-nrf next tactic should be a runTactic that takes some user input. Pass this
////  //input in as a list of strings where the runTactic request passes None.
////
//////  val nodeClosed = path("nodeClosed") undefCall
//////  val nodePruned = path("nodePruned") undefCall
//////  val limitExceeded = path("limitExceeded") undefCall
//////  val startingStrategy = path("startingStrategy") undefCall
//////  val applyTactic = path("applyTactic") undefCall
//////  val getNode = path("getNode") undefCall
////
////  val routes =
////    javascriptRoute ::
////    cssRoute ::
////    staticRoute ::
////    //Real stuff begins here.
////    getUpdates ::
////    startSession ::
////    startNewProblem ::
////    formulaToString ::
////    formulaToInteractiveString ::
////    formulaFromUid::
////    runTactic::
////    Nil
////
////  val myRoute = routes.reduce(_ ~ _)
////}
