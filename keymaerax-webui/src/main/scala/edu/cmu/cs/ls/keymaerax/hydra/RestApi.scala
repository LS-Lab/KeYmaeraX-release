/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.hydra

import _root_.edu.cmu.cs.ls.keymaerax.btactics.DerivationInfo
import akka.event.slf4j.SLF4JLogging
import edu.cmu.cs.ls.keymaerax.bellerophon._
import akka.actor.Actor
import spray.routing._
import spray.http._
import spray.json._
import spray.util.LoggingContext

class RestApiActor extends Actor with RestApi {
  implicit def eh(implicit log: LoggingContext) = ExceptionHandler {
    case e: Throwable => ctx =>
      val errorJson: String = new ErrorResponse(e.getMessage, e).getJson.prettyPrint
      log.error(e, s"Request '${ctx.request.uri}' resulted in uncaught exception", ctx.request)
      ctx.complete(StatusCodes.InternalServerError, errorJson)
  }

  def actorRefFactory = context

  //Note: separating the actor and router allows testing of the router without
  //spinning up an actor.
  def receive = runRoute(myRoute)

}

/**
 * RestApi is the API router. See README.md for a description of the API.
 */
trait RestApi extends HttpService with SLF4JLogging {
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

  private def standardCompletion(r: Request) : String = {
    val responses = r.getResultingResponses()
    //@note log all error responses
    responses.foreach({
      case e: ErrorResponse => log.warn("Error response details: " + e.msg, e.exn)
      case _ => /* nothing to do */
    })

    responses match {
      case hd :: Nil => hd.getJson.prettyPrint
      case _         => JsArray(responses.map(_.getJson):_*).prettyPrint
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
        complete(request.getResultingResponses().last.getJson.prettyPrint)
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
    require(responses.length == 1, "Should only have a single response.")
    complete(standardCompletion(request))
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

  val deleteModel = userPrefix {userId => pathPrefix("model" / Segment / "delete") { modelId => pathEnd {
    post {
      val r = new DeleteModelRequest(database, userId, modelId)
      complete(standardCompletion(r))
    }
  }}}

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

  val proofTasksParent = path("proofs" / "user" / Segment / Segment / Segment / "parent") { (userId, proofId, nodeId) => { pathEnd {
    get {
      val request = new ProofTaskParentRequest(database, userId, proofId, nodeId)
      complete(standardCompletion(request))
    }
  }}}

  val proofTasksPathAll = path("proofs" / "user" / Segment / Segment / Segment / "pathall") { (userId, proofId, nodeId) => { pathEnd {
    get {
      val request = new GetPathAllRequest(database, userId, proofId, nodeId)
      complete(standardCompletion(request))
    }
  }}}

  val proofTasksBranchRoot = path("proofs" / "user" / Segment / Segment / Segment / "branchroot") { (userId, proofId, nodeId) => { pathEnd {
    get {
      val request = new GetBranchRootRequest(database, userId, proofId, nodeId)
      complete(standardCompletion(request))
    }
  }}}

  /* Strictly positive position = SuccPosition, strictly negative = AntePosition, 0 not used */
  def parseFormulaId(id:String): Position = {
    val (idx :: inExprs) = id.split(',').toList.map({case str => str.toInt})
    try { Position(idx, inExprs) }
    catch {
      case e: IllegalArgumentException =>
        throw new Exception("Invalid formulaId " + id + " in axiomList").initCause(e)
    }
  }

  val axiomList = path("proofs" / "user" / Segment / Segment / Segment / Segment / "list") { (userId, proofId, nodeId, formulaId) => { pathEnd {
    get {
      val request = new GetApplicableAxiomsRequest(database, userId, proofId, nodeId, parseFormulaId(formulaId))
      complete(standardCompletion(request))
    }
  }}}

  val twoPosList = path("proofs" / "user" / Segment / Segment / Segment / Segment / Segment / "twoposlist") { (userId, proofId, nodeId, fml1Id, fml2Id) => { pathEnd {
    get {
      val request = new GetApplicableTwoPosTacticsRequest(database, userId, proofId, nodeId, parseFormulaId(fml1Id), parseFormulaId(fml2Id))
      complete(standardCompletion(request))
    }
  }}}

  val doAt = path("proofs" / "user" / Segment / Segment / Segment / Segment / "doAt" / Segment) { (userId, proofId, nodeId, formulaId, tacticId) => { pathEnd {
    get {
      val request = new RunBelleTermRequest(database, userId, proofId, nodeId, tacticId, Some(Fixed(parseFormulaId(formulaId))))
      complete(standardCompletion(request))
    }}
  }}

  val doInputAt = path("proofs" / "user" / Segment / Segment / Segment / Segment / "doInputAt" / Segment) { (userId, proofId, nodeId, formulaId, tacticId) => { pathEnd {
    post {
      entity(as[String]) { params => {
        val info = DerivationInfo(tacticId)
        val expectedInputs = info.inputs
        // Input has format [{"type":"formula","param":"j(x)","value":"v >= 0"}]
        val paramArray = JsonParser(params).asInstanceOf[JsArray]
        val inputs =
          paramArray.elements.map({case elem =>
            val obj = elem.asJsObject()
            val paramName = obj.getFields("param").head.asInstanceOf[JsString].value
            val paramValue = obj.getFields("value").head.asInstanceOf[JsString].value
            val paramInfo = expectedInputs.find{case spec => spec.name == paramName}
            BelleTermInput(paramValue, paramInfo)
          })
        val request = new RunBelleTermRequest(database, userId, proofId, nodeId, tacticId, Some(Fixed(parseFormulaId(formulaId))), None, inputs.toList)
        complete(standardCompletion(request))
      }
    }}
  }}}

  val doTwoPosAt = path("proofs" / "user" / Segment / Segment / Segment / Segment / Segment / "doAt" / Segment) { (userId, proofId, nodeId, fml1Id, fml2Id, tacticId) => { pathEnd {
    get {
      val request = new RunBelleTermRequest(database, userId, proofId, nodeId, tacticId,
        Some(Fixed(parseFormulaId(fml1Id))), Some(Fixed(parseFormulaId(fml2Id))))
      complete(standardCompletion(request))
    }}
  }}

  val doTactic = path("proofs" / "user" / Segment / Segment / Segment / "do" / Segment) { (userId, proofId, nodeId, tacticId) => { pathEnd {
    get {
      val request = new RunBelleTermRequest(database, userId, proofId, nodeId, tacticId, None)
      complete(standardCompletion(request))
    }}
  }}

  val doCustomTactic = path("proofs" / "user" / Segment / Segment / Segment / "doCustomTactic") { (userId, proofId, nodeId) => { pathEnd {
    post {
      entity(as[String]) { tactic => {
        val request = new RunBelleTermRequest(database, userId, proofId, nodeId, tactic, None, consultAxiomInfo=false)
        complete(standardCompletion(request))
      }}
    }}
  }}

  import Find._
  val doSearchRight = path("proofs" / "user" / Segment / Segment / Segment / "doSearchR" / Segment) { (userId, proofId, goalId, tacticId) => { pathEnd {
    get {
      val request = new RunBelleTermRequest(database, userId, proofId, goalId, tacticId, Some(FindR(0, None)))
      complete(standardCompletion(request))
    }}
  }}

  val doSearchLeft = path("proofs" / "user" / Segment / Segment / Segment / "doSearchL" / Segment) { (userId, proofId, goalId, tacticId) => { pathEnd {
    get {
      val request = new RunBelleTermRequest(database, userId, proofId, goalId, tacticId, Some(FindL(0, None)))
      complete(standardCompletion(request))
    }}
  }}

  val taskStatus = path("proofs" / "user" / Segment / Segment / Segment / Segment / "status") { (userId, proofId, nodeId, taskId) => { pathEnd {
    get {
      val request = new TaskStatusRequest(database, userId, proofId, nodeId, taskId)
      complete(standardCompletion(request))
    }}
  }}

  val taskResult = path("proofs" / "user" / Segment / Segment / Segment / Segment / "result") { (userId, proofId, nodeId, taskId) => { pathEnd {
    get {
      val request = new TaskResultRequest(database, userId, proofId, nodeId, taskId)
      complete(standardCompletion(request))
    }}
  }}

  val stopTask = path("proofs" / "user" / Segment / Segment / Segment / Segment / "stop") { (userId, proofId, nodeId, taskId) => { pathEnd {
    get {
      val request = new StopTaskRequest(database, userId, proofId, nodeId, taskId)
      complete(standardCompletion(request))
    }}
  }}

  val pruneBelow = path("proofs" / "user" / Segment / Segment / Segment / "pruneBelow") { (userId, proofId, nodeId) => { pathEnd {
    get {
      val request = new PruneBelowRequest(database, userId, proofId, nodeId)
      complete(standardCompletion(request))
    }
  }}}

  val proofTask = path("proofs" / "user" / Segment / Segment / "agendaDetails" / Segment.?) { (userId, proofId, nodeId) => { pathEnd {
    get {
      val request = new GetProofNodeInfoRequest(database, userId, proofId, nodeId)
      complete(standardCompletion(request))
    }
  }}}

  val getAgendaItem = path("proofs" / "user" / Segment / Segment / "agendaItem" / Segment) { (userId, proofId, nodeId) => { pathEnd {
    get {
      val request = new GetAgendaItemRequest(database, userId, proofId, nodeId)
      complete(standardCompletion(request))
    }}}}

  val setAgendaItemName = path("proofs" / "user" / Segment / Segment / Segment / "name" / Segment) { (userId, proofId, nodeId, newName) => { pathEnd {
    post {
      entity(as[String]) { params => {
        val request = new SetAgendaItemNameRequest(database, userId, proofId, nodeId, newName)
        complete(standardCompletion(request))
    }}}}}}


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

  val counterExample = path("proofs" / "user" / Segment / Segment / Segment / "counterExample") { (userId, proofId, nodeId) => {
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

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Server management
  //////////////////////////////////////////////////////////////////////////////////////////////////

  val isLocal = path("isLocal") { pathEnd { get {
    complete(standardCompletion(new IsLocalInstanceRequest()))
  }}}

  val shutdown = path("shutdown") { pathEnd { get {
    complete(standardCompletion(new ShutdownReqeuest()))
  }}}

  val extractdb = path("extractdb") { pathEnd { post {
      complete(standardCompletion(new ExtractDatabaseRequest()))
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
    deleteModel           ::
    cookieecho            ::
    createProof           ::
    proofListForModel     ::
    proofList             ::
    openProof             ::
    getAgendaItem         ::
    setAgendaItemName     ::
    proofLoadStatus       ::
    changeProofName       ::
    proofProgressStatus   ::
    proofCheckIsProved    ::
    proofTasksNew         ::
    proofTasksParent      ::
    proofTasksPathAll     ::
    proofTasksBranchRoot  ::
    axiomList             ::
    twoPosList            ::
    doAt                  ::
    doTwoPosAt            ::
    doInputAt             ::
    doTactic              ::
    doCustomTactic        ::
    doSearchLeft          ::
    doSearchRight         ::
    taskStatus            ::
    taskResult            ::
    stopTask              ::
    counterExample        ::
    pruneBelow            ::
    proofTask             ::
    proofTree             ::
    devAction             ::
    sequent               ::
    dashInfo              ::
    kyxConfig             ::
    keymaeraXVersion      ::
    mathematicaConfig     ::
    mathematicaStatus     ::
    mathematicaConfigSuggestion ::
    license :: isLocal :: extractdb :: shutdown ::
    Nil
  val myRoute = routes.reduce(_ ~ _)
}
