/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.hydra

import java.security.SecureRandom
import java.util.{Calendar, Date}

import akka.event.slf4j.SLF4JLogging
import akka.actor.{Actor, ActorContext}
import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.DerivationInfo
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser
import spray.http.CacheDirectives.{`max-age`, `no-cache`}
import spray.http.HttpHeaders.`Cache-Control`
import spray.routing._
import spray.http._
import spray.json._
import spray.routing
import spray.util.LoggingContext
import spray.http.StatusCodes.{Forbidden, Unauthorized}
import spray.httpx.marshalling.ToResponseMarshallable

import scala.language.postfixOps

class RestApiActor extends Actor with RestApi {
  implicit def eh(implicit log: LoggingContext) = ExceptionHandler {
    case e: Throwable => ctx =>
      val errorJson: String = new ErrorResponse(e.getMessage, e).getJson.prettyPrint
      log.error(e, s"Request '${ctx.request.uri}' resulted in uncaught exception", ctx.request)
      ctx.complete(StatusCodes.InternalServerError, errorJson)
  }

  def actorRefFactory: ActorContext = context

  //Note: separating the actor and router allows testing of the router without
  //spinning up an actor.
  def receive: Actor.Receive = runRoute(myRoute)

}

/**
 * RestApi is the API router. See README.md for a description of the API.
 */
trait RestApi extends HttpService with SLF4JLogging {
  private val database = DBAbstractionObj.defaultDatabase //SQLite //Not sure when or where to create this... (should be part of Boot?)
  private val DEFAULT_ARCHIVE_LOCATION = "http://keymaerax.org/KeYmaeraX-projects/"
  private val BUNDLED_ARCHIVE_DIR = "/keymaerax-projects/"
  private val BUNDLED_ARCHIVE_LOCATION = s"classpath:${BUNDLED_ARCHIVE_DIR}"

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

  /**
    * Turn off all caching.
    *
    * @note A hosted version of the server should probably turn this off.
    * */
  private def completeWithoutCache(response: String) =
    respondWithHeader(`Cache-Control`(Seq(`no-cache`, `max-age`(0)))) {
      super.complete(response)
    }

  private def completeRequest(r: Request, t: SessionToken) = t match {
    case NewlyExpiredToken(_) => complete(Unauthorized, Nil, s"Session $t expired")
    case _ =>
      if (r.permission(t)) complete(standardCompletion(r, t))
      else complete(Forbidden, Nil, s"Permission to this resource (${r.getClass.getCanonicalName}) is denied for session $t")
  }

  private def standardCompletion(r: Request, t: SessionToken): ToResponseMarshallable = t match {
    case NewlyExpiredToken(_) => throw new AssertionError("Expired tokens are not standard request completions, use completeRequest instead")
    case _ =>
      val responses = r.getResultingResponses(t)
      completeResponse(responses)
  }

  /** @note you probably don't actually want to use this. Use standardCompletion instead. */
  private def completeResponse(responses: List[Response]): ToResponseMarshallable  = {
    //@note log all error responses
    responses.foreach({
      case e: ErrorResponse => log.warn("Error response details: " + e.msg, e.exn)
      case _ => /* nothing to do */
    })

    responses match {
      case hd :: Nil => hd.print
      case _         => JsArray(responses.map(_.getJson):_*).compactPrint
    }
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Begin Routing
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //Some common partials.
  private val userPrefix = pathPrefix("user" / Segment)

  private val denied = path("private" / "KeyStore.jks") { get { getFromResource("index_bootstrap.html") } }

  //The static directory.
  private val staticRoute =
    pathPrefix("") { get {
      respondWithHeader(`Cache-Control`(Seq(`no-cache`, `max-age`(0)))) {
        getFromResourceDirectory("")
      }
    }}
  private val homePage = path("") { get {
    respondWithHeader(`Cache-Control`(Seq(`no-cache`, `max-age`(0)))) {
      getFromResource("index_bootstrap.html")
    }
  }}


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Users
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  val users: Route = pathPrefix("user" / Segment / Segment / "mode" / Segment) { (username, password, mode) => {
    implicit val sessionUser = None
    pathEnd {
      get {
        val request = new LoginRequest(database,username, password)
        completeRequest(request, EmptyToken())
      } ~
      post {
        val request = new CreateUserRequest(database, username, password, mode)
        completeRequest(request, EmptyToken())
      }
    }
  }}

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Models
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // FYI to get cookies do this:
  val cookie_echo: Route = pathPrefix("cookie_echo" / Segment) { cookieName => cookie(cookieName) { cookieValue => {
    complete(cookieName + ": " + cookieValue.content)
  }}}

  val userTheme: SessionToken=>Route = (t: SessionToken) => path("users" / Segment / "theme") { userId => pathEnd {
    get {
      val request = new GetUserThemeRequest(database, userId)
      completeRequest(request, t)
    } ~
      post {
        entity(as[String]) { themeStr => {
          val theme = themeStr.parseJson.asJsObject.fields.map({case (k,v) => k -> v.toString})
          val request = new SetUserThemeRequest(database, userId, theme("css"), theme("fontSize"))
          completeRequest(request, t)
        }}}
  }}

  // GET /models/user returns a list of all models belonging to this user. The cookie must be set.
  val modelList: SessionToken=>Route = (t : SessionToken) => pathPrefix("models" / "users" / Segment) {userId => { pathEnd { get {
    val request = new GetModelListRequest(database, userId)
    completeRequest(request, t)
  }}}}

  //POST /users/<user id>/model/< name >/< keyFile >
  val userModel: SessionToken=>Route = (t : SessionToken) => userPrefix {userId => {pathPrefix("model" / Segment) {modelNameOrId => {pathEnd {
    post {
      entity(as[MultipartFormData]) { formData => {
        if(formData.fields.length > 1) ??? //should only have a single file.
        val data = formData.fields.last
        val contents = getFileContentsFromFormData(data)
        val request = new CreateModelRequest(database, userId, modelNameOrId, contents)
        completeRequest(request, t)
      }}
    } ~
    get {
      val request = new GetModelRequest(database, userId, modelNameOrId)
      completeRequest(request, t)
    }
  }}}}}

  val updateUserModel: SessionToken=>Route = (t: SessionToken) => userPrefix { userId => pathPrefix("model" / Segment / "update") { modelId => pathEnd {
    post {
      entity(as[String]) { modelJson =>
        val modelData = modelJson.parseJson.asJsObject.fields.map({case (k,v) => k -> v.asInstanceOf[JsString].value})
        completeRequest(new UpdateModelRequest(database, userId, modelId, modelData("name"),
          modelData("title"), modelData("description"), modelData("content")), t)
      }
    }
  }}}

  val userModelFromFormula: SessionToken=>Route = (t : SessionToken) => userPrefix {userId => {pathPrefix("modelFromFormula" / Segment) {modelName => {pathEnd {
    post {
      entity(as[String]) {formula => {
        val request = new CreateModelFromFormulaRequest(database, userId, modelName, formula)
        completeRequest(request, t)
      }}
    }
  }}}}}

  val importExampleRepo: SessionToken=>Route = (t: SessionToken) => path("models" / "users" / Segment / "importRepo") { (userId) => { pathEnd {
    post {
      entity(as[String]) { repoUrl => {
        val r = new ImportExampleRepoRequest(database, userId, repoUrl)
        completeRequest(r, t)
      }}
    }
  }}}

  val deleteModel: SessionToken=>Route = (t : SessionToken) => userPrefix {userId => pathPrefix("model" / Segment / "delete") { modelId => pathEnd {
    post {
      val r = new DeleteModelRequest(database, userId, modelId)
      completeRequest(r, t)
    }
  }}}

  val deleteModelProofs: SessionToken=>Route = (t : SessionToken) => userPrefix {userId => pathPrefix("model" / Segment / "deleteProofs") { modelId => pathEnd {
    post {
      val r = new DeleteModelProofsRequest(database, userId, modelId)
      completeRequest(r, t)
    }
  }}}

  val deleteProof: SessionToken=>Route = (t : SessionToken) => userPrefix {userId => pathPrefix("proof" / Segment / "delete") { proofId => pathEnd {
    post {
      val r = new DeleteProofRequest(database, userId, proofId)
      completeRequest(r, t)
    }
  }}}

  val modelplex: SessionToken=>Route = (t : SessionToken) => userPrefix {userId => pathPrefix("model" / Segment / "modelplex" / "generate" / Segment / Segment / Segment / Segment) { (modelId, artifact, monitorKind, monitorShape, conditionKind) => pathEnd {
    get {
      parameters('vars.as[String] ?) { vars => {
        val theVars: List[String] = vars match {
          case Some(v) => v.parseJson match {
            case a: JsArray => a.elements.map({ case JsString(s) => s}).toList
          }
          case None => List.empty
        }
        val r = new ModelPlexRequest(database, userId, modelId, artifact, monitorKind, monitorShape, conditionKind, theVars)
        completeRequest(r, t)
    }}}
  }}}

  val modelplexMandatoryVars: SessionToken=>Route = (t : SessionToken) => userPrefix {userId => pathPrefix("model" / Segment / "modelplex" / "mandatoryVars") { modelId => pathEnd {
    get {
      val r = new ModelPlexMandatoryVarsRequest(database, userId, modelId)
      completeRequest(r, t)
    }
  }}}

  val testSynthesis: SessionToken=>Route = (t : SessionToken) => userPrefix {userId => pathPrefix("model" / Segment / "testcase" / "generate" / Segment / Segment / Segment ) { (modelId, monitorKind, amount, timeout) => pathEnd {
    get {
      parameters('kinds.as[String] ?) { kinds => {
        val theKinds: Map[String,Boolean] = kinds match {
          case Some(v) => v.parseJson.asJsObject.fields.map({case (k, JsBoolean(v)) => k -> v})
        }
      val to = timeout match { case "0" => None case s => Some(Integer.parseInt(s)) }
      val r = new TestSynthesisRequest(database, userId, modelId, monitorKind, theKinds, Integer.parseInt(amount), to)
      completeRequest(r, t)
    }}}
  }}}

  //Because apparently FTP > modern web.
  val userModel2: SessionToken=>Route = (t : SessionToken) => userPrefix {userId => {pathPrefix("modeltextupload" / Segment) {modelNameOrId =>
  {pathEnd {
    post {
      entity(as[String]) { contents => {
        val request = new CreateModelRequest(database, userId, modelNameOrId, contents)
        completeRequest(request, t)
      }}}}}}}}

  //@note somehow wouldn't match without trailing /
  val uploadArchive: SessionToken=>Route = (t : SessionToken) => path("user" / Segment / "archiveupload" /) { userId => pathEnd {
    post {
      entity(as[String]) { contents => {
        val request = new UploadArchiveRequest(database, userId, contents)
        completeRequest(request, t)
      }}}
  }}

  val modelTactic: SessionToken=>Route = (t : SessionToken) => path("user" / Segment / "model" / Segment / "tactic") { (userId, modelId) => pathEnd {
    get {
      val request = new GetModelTacticRequest(database, userId, modelId)
      completeRequest(request, t)
    } ~
    post {
      entity(as[String]) { contents => {
        val request = new AddModelTacticRequest(database, userId, modelId, contents)
        completeRequest(request, t)
      }}}
  }}

  val extractTactic: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "extract") { (_, proofId) => { pathEnd {
    get {
      val request = new ExtractTacticRequest(database, proofId)
      completeRequest(request, t)
    }
  }}}

  val tacticDiff: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "tacticDiff") { (_, _) => { pathEnd {
    post {
      entity(as[String]) { contents => {
        val tactics = contents.parseJson.asJsObject
        val request = new TacticDiffRequest(database, tactics.fields("old").asInstanceOf[JsString].value, tactics.fields("new").asInstanceOf[JsString].value)
        completeRequest(request, t)
      }}}
  }}}

  val extractLemma: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "lemma") { (userId, proofId) => { pathEnd {
    get {
      val request = new ExtractLemmaRequest(database, userId, proofId)
      completeRequest(request, t)
    }
  }}}

  val downloadProblemSolution: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "download") { (userId, proofId) => { pathEnd {
    get {
      val request = new ExtractProblemSolutionRequest(database, userId, proofId)
      completeRequest(request, t)
    }
  }}}

  val downloadModelProofs: SessionToken=>Route = (t : SessionToken) => path("models" / "user" / Segment / "model" / Segment / "downloadProofs") { (userId, modelId) => { pathEnd {
    get {
      val request = new ExtractModelSolutionsRequest(database, userId, Integer.parseInt(modelId) :: Nil,
        withProofs = true, exportEmptyProof = true)
      completeRequest(request, t)
    }
  }}}

  val downloadAllProofs: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / "downloadAllProofs") { userId => { pathEnd {
    get {
      //@note potential performance bottleneck: loads all models just to get ids
      val allModels = database.getModelList(userId).map(_.modelId)
      val request = new ExtractModelSolutionsRequest(database, userId, allModels, withProofs = true, exportEmptyProof = false)
      completeRequest(request, t)
    }
  }}}

  val downloadAllModels: SessionToken=>Route = (t : SessionToken) => path("models" / "user" / Segment / "downloadAllModels" / Segment) { (userId, proofs) => { pathEnd {
    get {
      val allModels = database.getModelList(userId).map(_.modelId)
      val request = new ExtractModelSolutionsRequest(database, userId, allModels,
        withProofs = proofs == "withProofs", exportEmptyProof = true)
      completeRequest(request, t)
    }
  }}}

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Proofs
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  val createProof: SessionToken=>Route = (t: SessionToken) => path("models" / "users" / Segment / "model" / Segment / "createProof") { (userId, modelId) => { pathEnd {
    post {
      entity(as[String]) { x => {
        val obj = x.parseJson
        val submittedProofName = obj.asJsObject.getFields("proofName").last.asInstanceOf[JsString].value
        val proofName = if (submittedProofName == "") {
          val model = database.getModel(modelId)
          model.name + ": Proof " + (model.numProofs + 1)
        } else submittedProofName
        val proofDescription = obj.asJsObject.getFields("proofDescription").last.asInstanceOf[JsString].value

        val request = new CreateProofRequest(database, userId, modelId, proofName, proofDescription)
        completeRequest(request, t)
      }}
    }
  }}}

  val createModelTacticProof: SessionToken=>Route = (t: SessionToken) => path("models" / "users" / Segment / "model" / Segment / "createTacticProof") { (userId, modelId) => { pathEnd {
    post {
      entity(as[String]) { _ => {
        val request = new CreateModelTacticProofRequest(database, userId, modelId)
        completeRequest(request, t)
      }}
    }
  }}}

  val proofListForModel: SessionToken=>Route = (t: SessionToken) => path("models" / "users" / Segment / "model" / Segment / "proofs") { (userId, modelId) => { pathEnd {
    get {
      val request = new ProofsForModelRequest(database, userId, modelId)
      completeRequest(request, t)
    }
  }}}

  val proofList: SessionToken=>Route = (t: SessionToken) => path("models" / "users" / Segment / "proofs") { (userId) => { pathEnd {
    get {
      val request = new ProofsForUserRequest(database, userId)
      completeRequest(request, t)
    }
  }}}

  val openProof: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment) { (userId, proofId) => { pathEnd {
    get {
      val request = new OpenProofRequest(database, userId, proofId)
      completeRequest(request, t)
    }
  }}}

  val initProofFromTactic: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "initfromtactic") { (userId, proofId) => { pathEnd {
    get {
      val request = new InitializeProofFromTacticRequest(database, userId, proofId)
      completeRequest(request, t)
    }
  }}}

  val browseProofRoot: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "browseagenda") { (userId, proofId) => { pathEnd {
    get {
      val request = new GetProofRootAgendaRequest(database, userId, proofId)
      completeRequest(request, t)
    }
  }}}

  val browseNodeChildren: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "browseChildren") { (userId, proofId, nodeId) => { pathEnd {
    get {
      val request = new GetProofNodeChildrenRequest(database, userId, proofId, nodeId)
      completeRequest(request, t)
    }
  }}}

  val proofTasksNew: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "agendaawesome") { (userId, proofId) => { pathEnd {
    get {
      val request = new GetAgendaAwesomeRequest(database, userId, proofId)
      completeRequest(request, t)
    }
  }}}

  val proofTasksParent: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "parent") { (userId, proofId, nodeId) => { pathEnd {
    get {
      val request = new ProofTaskParentRequest(database, userId, proofId, nodeId)
      completeRequest(request, t)
    }
  }}}

  val proofTasksPathAll: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "pathall") { (userId, proofId, nodeId) => { pathEnd {
    get {
      val request = new GetPathAllRequest(database, userId, proofId, nodeId)
      completeRequest(request, t)
    }
  }}}

  val proofTasksBranchRoot: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "branchroot") { (userId, proofId, nodeId) => { pathEnd {
    get {
      val request = new GetBranchRootRequest(database, userId, proofId, nodeId)
      completeRequest(request, t)
    }
  }}}

  val proofTaskExpand: SessionToken => Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "expand") { (userId, proofId, nodeId) => { pathEnd {
    get {
      val request = new ProofTaskExpandRequest(database, userId, proofId, nodeId)
      completeRequest(request, t)
    }
  }}}

  val proofNodeSequent: SessionToken => Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "sequent") { (userId, proofId, nodeId) => { pathEnd {
    get {
      val request = new ProofNodeSequentRequest(database, userId, proofId, nodeId)
      completeRequest(request, t)
    }
  }}}

  val stepwiseTrace: SessionToken => Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "trace") { (userId, proofId) => { pathEnd {
    get {
      val request = new StepwiseTraceRequest(database, userId, proofId)
      completeRequest(request, t)
    }
  }}}

  /* Strictly positive position = SuccPosition, strictly negative = AntePosition, 0 not used */
  def parseFormulaId(id:String): Position = {
    val (idx :: inExprs) = id.split(',').toList.map(_.toInt)
    try { Position(idx, inExprs) }
    catch {
      case e: IllegalArgumentException =>
        throw new Exception("Invalid formulaId " + id + " in axiomList").initCause(e)
    }
  }

  val axiomList: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / Segment / "list") { (userId, proofId, nodeId, formulaId) => { pathEnd {
    get {
      val request = new GetApplicableAxiomsRequest(database, userId, proofId, nodeId, parseFormulaId(formulaId))
      completeRequest(request, t)
    }
  }}}

  val sequentList: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "listStepSuggestions") { (userId, proofId, nodeId) => { pathEnd {
    get {
      val request = new GetSequentStepSuggestionRequest(database, userId, proofId, nodeId)
      completeRequest(request, t)
    }
  }}}

  val twoPosList: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / Segment / Segment / "twoposlist") { (userId, proofId, nodeId, fml1Id, fml2Id) => { pathEnd {
    get {
      val request = new GetApplicableTwoPosTacticsRequest(database, userId, proofId, nodeId, parseFormulaId(fml1Id), parseFormulaId(fml2Id))
      completeRequest(request, t)
    }
  }}}

  val derivationInfo: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "derivationInfos" / Segment) { (userId, proofId, nodeId, axiomId) => { pathEnd {
    get {
      val request = new GetDerivationInfoRequest(database, userId, proofId, nodeId, axiomId)
      completeRequest(request, t)
    }
  }}}

  val exportSequent: SessionToken=>Route = (t: SessionToken) => path("proofs" / "user" / "export" / Segment / Segment / Segment) { (userId, proofId, nodeId) => { pathEnd {
    get {
      val request = new ExportCurrentSubgoal(database, userId, proofId, nodeId)
      completeRequest(request, t)
    }
  }}}

  val doAt: SessionToken=>Route = (t: SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / Segment / "doAt" / Segment) { (userId, proofId, nodeId, formulaId, tacticId) => { pathEnd {
    get { parameters('stepwise.as[Boolean]) { stepwise =>
      val request = new RunBelleTermRequest(database, userId, proofId, nodeId, tacticId, Some(Fixed(parseFormulaId(formulaId))), None, Nil, consultAxiomInfo=true, stepwise=stepwise)
      completeRequest(request, t)
    }}}
  }}

  val getStep: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / Segment / "whatStep") { (userId, proofId, nodeId, formulaId) => { pathEnd {
    get {
      val request = new GetStepRequest(database, userId, proofId, nodeId, parseFormulaId(formulaId))
      completeRequest(request, t)
    }}
  }}

  val searchLemmas: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / Segment / "lemmas" / Segment) { (userId, proofId, nodeId, formulaId, partialLemmaName) => { pathEnd {
    get {
      val request = new GetLemmasRequest(database, userId, proofId, nodeId, parseFormulaId(formulaId), partialLemmaName)
      completeRequest(request, t)
    }}
  }}

  val formulaPrettyString: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / Segment / "prettyString") { (userId, proofId, nodeId, formulaId) => { pathEnd {
    get {
      val request = new GetFormulaPrettyStringRequest(database, userId, proofId, nodeId, parseFormulaId(formulaId))
      completeRequest(request, t)
    }}
  }}

  val checkInput: SessionToken=>Route = (t: SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "checkInput" / Segment) { (userId, proofId, nodeId, tacticId) => { pathEnd {
    get {
      parameters('param, 'type, 'value) { (pName, pType, pValue) =>
        completeRequest(new CheckTacticInputRequest(database, userId, proofId, nodeId, tacticId, pName, pType, pValue), t)
      }
    }
  }}}

  val doInputAt: SessionToken=>Route = (t: SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / Segment / "doInputAt" / Segment) { (userId, proofId, nodeId, formulaId, tacticId) => { pathEnd {
    post {
      parameters('stepwise.as[Boolean]) { stepwise => entity(as[String]) { params => {
        val info = DerivationInfo(tacticId)
        val expectedInputs = info.inputs
        // Input has format [{"type":"formula","param":"j(x)","value":"v >= 0"}]
        val paramArray = JsonParser(params).asInstanceOf[JsArray].elements.map(_.asJsObject())
        val illFormedParams = paramArray.filter({obj =>
          val paramName = obj.getFields("param").head.asInstanceOf[JsString].value
          val paramInfo = expectedInputs.find(_.name == paramName)
          paramInfo.isEmpty || obj.getFields("value").isEmpty
        })
        if (illFormedParams.isEmpty) {
          val inputs =
            paramArray.map({ obj =>
              val paramName = obj.getFields("param").head.asInstanceOf[JsString].value
              val paramValue = obj.getFields("value").head.asInstanceOf[JsString].value
              val paramInfo = expectedInputs.find(_.name == paramName)
              BelleTermInput(paramValue, paramInfo)
            })
          val request = new RunBelleTermRequest(database, userId, proofId, nodeId, tacticId,
            Some(Fixed(parseFormulaId(formulaId))), None, inputs.toList, consultAxiomInfo=true, stepwise=stepwise)
          completeRequest(request, t)
        } else {
          val missing = illFormedParams.map(_.getFields("param").head.asInstanceOf[JsString].value).mkString(", ")
          completeRequest(new FailedRequest(userId, "Ill-formed tactic arguments, missing parameters " + missing), t)
        }
      }
    }}}
  }}}

  val doTwoPosAt: SessionToken=>Route = (t: SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / Segment / Segment / "doAt" / Segment) { (userId, proofId, nodeId, fml1Id, fml2Id, tacticId) => { pathEnd {
    get { parameters('stepwise.as[Boolean]) { stepwise =>
      val request = new RunBelleTermRequest(database, userId, proofId, nodeId, tacticId,
        Some(Fixed(parseFormulaId(fml1Id))), Some(Fixed(parseFormulaId(fml2Id))), Nil, consultAxiomInfo=true, stepwise=stepwise)
      completeRequest(request, t)
    }}}
  }}

  val doTactic: SessionToken=>Route = (t: SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "do" / Segment) { (userId, proofId, nodeId, tacticId) => { pathEnd {
    get { parameters('stepwise.as[Boolean]) { stepwise =>
      val request = new RunBelleTermRequest(database, userId, proofId, nodeId, tacticId, None, None, Nil, consultAxiomInfo=true, stepwise=stepwise)
      completeRequest(request, t)
    }}}
  }}

  val doInputTactic: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "doInput" / Segment) { (userId, proofId, nodeId, tacticId) => { pathEnd {
    post { parameters('stepwise.as[Boolean]) { stepwise =>
      entity(as[String]) { params => {
        val info = DerivationInfo(tacticId)
        val expectedInputs = info.inputs
        // Input has format [{"type":"formula","param":"j(x)","value":"v >= 0"}]
        val paramArray = JsonParser(params).asInstanceOf[JsArray]
        val inputs =
          paramArray.elements.map({ elem =>
            val obj = elem.asJsObject()
            val paramName = obj.getFields("param").head.asInstanceOf[JsString].value
            val paramValue = obj.getFields("value").head.asInstanceOf[JsString].value
            val paramInfo = expectedInputs.find(_.name == paramName)
            BelleTermInput(paramValue, paramInfo)
          })
        val request = new RunBelleTermRequest(database, userId, proofId, nodeId, tacticId, None, None, inputs.toList, consultAxiomInfo=true, stepwise=stepwise)
        completeRequest(request, t)
      }
      }}}
  }}}

  val doCustomTactic: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "doCustomTactic") { (userId, proofId, nodeId) => { pathEnd {
    post { parameters('stepwise.as[Boolean]) { stepwise =>
      entity(as[String]) { tactic => {
        val request = new RunBelleTermRequest(database, userId, proofId, nodeId, tactic, None, consultAxiomInfo=false, stepwise=stepwise)
        completeRequest(request, t)
      }}
    }}}
  }}

  val doSearch: SessionToken=>Route = (t: SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "doSearch" / Segment / Segment) { (userId, proofId, goalId, where, tacticId) => { pathEnd {
    get { parameters('stepwise.as[Boolean]) { stepwise =>
      val pos = where match {
        case "R" => Find.FindR(0, None)
        case "L" => Find.FindL(0, None)
        case loc => throw new IllegalArgumentException("Unknown position locator " + loc)
      }
      val request = new RunBelleTermRequest(database, userId, proofId, goalId, tacticId, Some(pos), None, Nil, consultAxiomInfo=true, stepwise=stepwise)
      completeRequest(request, t)
    }} ~
    post { parameters('stepwise.as[Boolean]) { stepwise =>
      entity(as[String]) { params => {
        val info = DerivationInfo(tacticId)
        val expectedInputs = info.inputs
        // Input has format [{"type":"formula","param":"j(x)","value":"v >= 0"}]
        val paramArray = JsonParser(params).asInstanceOf[JsArray]
        val inputs =
          paramArray.elements.map({elem =>
            val obj = elem.asJsObject()
            val paramName = obj.getFields("param").head.asInstanceOf[JsString].value
            val paramValue = obj.getFields("value").head.asInstanceOf[JsString].value
            val paramInfo = expectedInputs.find(_.name == paramName)
            BelleTermInput(paramValue, paramInfo)
          })
        val pos = where match {
          case "R" => Find.FindR(0, None)
          case "L" => Find.FindL(0, None)
          case loc => throw new IllegalArgumentException("Unknown position locator " + loc)
        }
        val request = new RunBelleTermRequest(database, userId, proofId, goalId, tacticId, Some(pos), None, inputs.toList, consultAxiomInfo=true, stepwise=stepwise)
        completeRequest(request, t)
      }
      }}}
    }
  }}

  val taskStatus: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / Segment / "status") { (userId, proofId, nodeId, taskId) => { pathEnd {
    get {
      val request = new TaskStatusRequest(database, userId, proofId, nodeId, taskId)
      completeRequest(request, t)
    }}
  }}

  val taskResult: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / Segment / "result") { (userId, proofId, nodeId, taskId) => { pathEnd {
    get {
      val request = new TaskResultRequest(database, userId, proofId, nodeId, taskId)
      completeRequest(request, t)
    }}
  }}

  val stopTask: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / Segment / "stop") { (userId, proofId, nodeId, taskId) => { pathEnd {
    get {
      val request = new StopTaskRequest(database, userId, proofId, nodeId, taskId)
      completeRequest(request, t)
    }}
  }}

  val pruneBelow: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "pruneBelow") { (userId, proofId, nodeId) => { pathEnd {
    get {
      val request = new PruneBelowRequest(database, userId, proofId, nodeId)
      completeRequest(request, t)
    }
  }}}

  val getAgendaItem: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "agendaItem" / Segment) { (userId, proofId, nodeId) => { pathEnd {
    get {
      val request = GetAgendaItemRequest(database, userId, proofId, nodeId)
      completeRequest(request, t)
    }}}}

  val setAgendaItemName: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "name" / Segment) { (userId, proofId, nodeId, newName) => { pathEnd {
    post {
      entity(as[String]) { _ => {
        val request = SetAgendaItemNameRequest(database, userId, proofId, nodeId, newName)
        completeRequest(request, t)
    }}}}}}

  val proofProgressStatus: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "progress") { (userId, proofId) => { pathEnd {
    get {
      val request = new GetProofProgressStatusRequest(database, userId, proofId)
      completeRequest(request, t)
    }
  }}}

  val proofCheckIsProved: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "validatedStatus") { (userId, proofId) => { pathEnd {
    get {
      val request = new CheckIsProvedRequest(database, userId, proofId)
      completeRequest(request, t)
    }
  }}}

  val counterExample: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "counterExample") { (userId, proofId, nodeId) => {
    pathEnd {
      get {
        val request = new CounterExampleRequest(database, userId, proofId, nodeId)
        completeRequest(request, t)
      }
    }}
  }

  val setupSimulation: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "setupSimulation") { (userId, proofId, nodeId) => {
    pathEnd {
      get {
        val request = new SetupSimulationRequest(database, userId, proofId, nodeId)
        completeRequest(request, t)
      }
    }}
  }

  val simulate: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "simulate") { (userId, proofId, nodeId) => {
    pathEnd {
      post {
        entity(as[String]) { params => {
          val obj = JsonParser(params).asJsObject()
          val initial = obj.fields("initial").asInstanceOf[JsString].value.asFormula
          val stateRelation = obj.fields("stateRelation").asInstanceOf[JsString].value.asFormula
          val numSteps = obj.fields("numSteps").asInstanceOf[JsNumber].value.intValue()
          val stepDuration = obj.fields("stepDuration").asInstanceOf[JsString].value.asTerm
          val request = new SimulationRequest(database, userId, proofId, nodeId, initial, stateRelation, numSteps, 1, stepDuration)
          completeRequest(request, t)
        }}}
    }}
  }


  val logoff: SessionToken=>Route  = (t: SessionToken) => path("user" / "logoff") { pathEnd { get {
    t match {
      case ut: UserToken => SessionManager.remove(ut.token)
      case NewlyExpiredToken(_) => //Well, that was convienant.
      case _ => //that works too.
    }
    complete("[]")
  }}}

  val guestBrowseArchiveRequest: Route = path("show" / Segments) { archiveUri => pathEnd {
    get {
      val (archiveLocation: String, archiveRelativeLocation: String) = archiveUri match {
        case head::Nil if head.startsWith("http") || head.startsWith("https") => (head, head)
        case segments =>
          val path = segments.reduce(_+"/"+_)
          if (getClass.getResourceAsStream(BUNDLED_ARCHIVE_DIR + path) != null) (BUNDLED_ARCHIVE_LOCATION + path, path)
          else {
            println(s"Could not find ${BUNDLED_ARCHIVE_LOCATION + path} resource in JAR file. Accessing remote host.")
            (DEFAULT_ARCHIVE_LOCATION + path, path)
          }
      }
      val request = new OpenGuestArchiveRequest(database, archiveLocation, archiveRelativeLocation)
      completeRequest(request, EmptyToken())
    }
  }}

  val kyxConfig: Route = path("kyxConfig") {
    pathEnd {
      get {
        val request = new KyxConfigRequest(database)
        completeRequest(request, EmptyToken())
      }
    }
  }

  val keymaeraXVersion: Route = path("keymaeraXVersion") {
    pathEnd {
      get {
        val request = new KeymaeraXVersionRequest()
        completeRequest(request, EmptyToken())
      }
    }
  }

  val mathConfSuggestion: Route = path("config" / "mathematica" / "suggest") {
    pathEnd {
      get {
        val request = new GetMathematicaConfigSuggestionRequest(database)
        completeRequest(request, EmptyToken())
      }
    }
  }

  val tool: Route = path("config" / "tool") {
    pathEnd {
      get {
        val request = new GetToolRequest(database)
        completeRequest(request, EmptyToken())
      } ~
      post {
        entity(as[String]) { tool =>
          val request = new SetToolRequest(database, tool)
          completeRequest(request, EmptyToken())
        }
      }
    }
  }

  val mathematicaConfig: Route = path("config" / "mathematica") {
    pathEnd {
      get {
          val request = new GetMathematicaConfigurationRequest(database)
          completeRequest(request, EmptyToken())
      } ~
      post {
        entity(as[String]) { params => {
          val p = JsonParser(params).asJsObject.fields.map(param => param._1.toString -> param._2.asInstanceOf[JsString].value)
          assert(p.contains("linkName"), "linkName not in: " + p.keys.toString())
          assert(p.contains("jlinkLibDir"), "jlinkLibDir not in: " + p.keys.toString()) //@todo These are schema violations and should be checked as such, but I needed to disable the validator.
          val linkName : String = p("linkName")
          val jlinkLibDir : String = p("jlinkLibDir")
          val request = new ConfigureMathematicaRequest(database, linkName, jlinkLibDir)
          completeRequest(request, EmptyToken())
        }}
      }
    }
  }

  val toolStatus: Route = path("config" / "toolStatus") {
    pathEnd {
      get {
        Configuration(Configuration.Keys.QE_TOOL) match {
          case "mathematica" => completeRequest(new MathematicaStatusRequest(database), EmptyToken())
          case "z3" => completeRequest(new Z3StatusRequest(database), EmptyToken())
        }
      }
    }
  }

  val systemInfo: Route = path("config" / "systeminfo") {
    pathEnd {
      get {
        completeRequest(new SystemInfoRequest(database), EmptyToken())
      }
    }
  }

  val licenses: Route = path("licenses") {
    pathEnd {
      get {
        completeRequest(new LicensesRequest(), EmptyToken())
      }
    }
  }

  val examples: SessionToken=>Route = (t : SessionToken) => path("examples" / "user" / Segment / "all") { userId =>
    pathEnd {
      get {
        val request = new ListExamplesRequest(database, userId)
        completeRequest(request, t)
      }
    }
  }

  val runBelleTerm: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "nodes" / Segment / "tactics" / "runBelleTerm") { (userId, proofId, nodeId) => { pathEnd {
    post {
      entity(as[String]) { params => {
        val term = JsonParser(params).asJsObject.fields.last._2.asInstanceOf[JsString].value
        val request = new RunBelleTermRequest(database, userId, proofId, nodeId, term, None)
        completeRequest(request, t)
  }}}}}}

  val changeProofName: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "name" / Segment) { (userId, proofId, newName) => { pathEnd {
    post {
      entity(as[String]) { _ => {
        completeRequest(new UpdateProofNameRequest(database, userId, proofId, newName), t)
      }}
    }
  }}}

  val devAction: Route = path("dev" / Segment) { (action) => {
    get {
      assert(!HyDRAServerConfig.isHosted, "dev actions are only available on locally hosted instances.")
      if(action.equals("deletedb")) {
        database.cleanup()
        complete("{}")
      }
      else {
        complete("{}")
      }
    }
  }}

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Proof validation requests
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  /** Validates the proof of a lemma. */
  val validateProof: Route = path("validate") { pathEnd {
    post {
      entity(as[String]) { archiveFileContents => {
        val entries = KeYmaeraXArchiveParser.parse(archiveFileContents)

        if(entries.length != 1)
          complete(completeResponse(new ErrorResponse(s"Expected exactly one model in the archive but found ${entries.length}") :: Nil))
        else if(entries.head.tactics.length != 1)
          complete(completeResponse(new ErrorResponse(s"Expected exactly one proof in the archive but found ${entries.head.tactics.length} proofs. Make sure you export from the Proofs page, not the Models page.") :: Nil))
        else {
          val model = entries.head.model.asInstanceOf[Formula]
          val tactic = entries.head.tactics.head._2
          complete(standardCompletion(new ValidateProofRequest(database, model, tactic), EmptyToken()))
        }
      }}
    }
  }}

  val checkProofValidation: Route = path("validate" / Segment) { (taskId) => {
    get {
      complete(standardCompletion(new CheckValidationRequest(database, taskId), EmptyToken()))
    }
  }}

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Server management
  //////////////////////////////////////////////////////////////////////////////////////////////////

  val isLocal: Route = path("isLocal") { pathEnd { get {
    implicit val sessionUser = None
    completeRequest(new IsLocalInstanceRequest(), EmptyToken())
  }}}

  val shutdown: Route = path("shutdown") { pathEnd { get {
    implicit val sessionUser = None
    completeRequest(new ShutdownReqeuest(), EmptyToken())
  }}}

  val extractdb: Route = path("extractdb") { pathEnd { post {
    implicit val sessionUser = None
    completeRequest(new ExtractDatabaseRequest(), EmptyToken())
  }}}


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Licensing
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //@todo license acceptance per user
//  val license = path("licenseacceptance") {  {
//    get {
//      completeRequest(new IsLicenseAcceptedRequest(database), EmptyToken())
//    } ~
//    post {
//      completeRequest(new AcceptLicenseRequest(database), EmptyToken())
//    }
//  }}

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Route precedence
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  val publicRoutes: List[routing.Route] =
    denied ::
    staticRoute        ::
    homePage           ::
//    license            ::
    isLocal            ::
    extractdb          ::
    shutdown           ::
    users              ::
    cookie_echo        ::
    kyxConfig          ::
    keymaeraXVersion   ::
    mathematicaConfig  ::
    toolStatus         ::
    tool               ::
    guestBrowseArchiveRequest ::
    systemInfo         ::
    mathConfSuggestion ::
    devAction          ::
    checkProofValidation ::
    validateProof      ::
    licenses           ::
    Nil

  /** Requests that need a session token parameter.
    *
    * @see [[sessionRoutes]] is built by wrapping all of these sessions in a cookieOptional("session") {...} that extrtacts the cookie name. */
  private val partialSessionRoutes : List[SessionToken => routing.Route] =
    downloadAllModels     :: //@note before userModel2 to match correctly
    modelList             ::
    modelTactic           ::
    userModel             ::
    userModel2            ::
    deleteModel           ::
    createProof           ::
    createModelTacticProof::
    initProofFromTactic   ::
    importExampleRepo     ::
    deleteProof           ::
    proofListForModel     ::
    proofList             ::
    downloadAllProofs     :: //@note before openProof to match correctly
    downloadModelProofs   ::
    openProof             ::
    getAgendaItem         ::
    setAgendaItemName     ::
    changeProofName       ::
    proofProgressStatus   ::
    proofCheckIsProved    ::
    proofTasksNew         ::
    proofTasksParent      ::
    proofTasksPathAll     ::
    proofTasksBranchRoot  ::
    proofTaskExpand       ::
    proofNodeSequent      ::
    axiomList             ::
    sequentList           ::
    twoPosList            ::
    derivationInfo        ::
    doAt                  ::
    doTwoPosAt            ::
    doInputAt             ::
    checkInput            ::
    doTactic              ::
    doInputTactic         ::
    doCustomTactic        ::
    doSearch              ::
    getStep               ::
    searchLemmas          ::
    formulaPrettyString   ::
    taskStatus            ::
    taskResult            ::
    stopTask              ::
    extractTactic         ::
    tacticDiff            ::
    extractLemma          ::
    downloadProblemSolution ::
    counterExample        ::
    setupSimulation       ::
    simulate              ::
    pruneBelow            ::
    modelplex             ::
    modelplexMandatoryVars::
    exportSequent         ::
    testSynthesis         ::
    uploadArchive         ::
    userModelFromFormula  ::
    examples              ::
    stepwiseTrace         ::
    updateUserModel       ::
    userTheme             ::
    browseProofRoot       ::
    browseNodeChildren    ::
    deleteModelProofs     ::
    logoff                ::
    // DO NOT ADD ANYTHING AFTER LOGOFF!
    Nil

  val sessionRoutes : List[routing.Route] = partialSessionRoutes.map(routeForSession => optionalHeaderValueByName("x-session-token") {
    case Some(token) => routeForSession(SessionManager.token(token))
    case None => routeForSession(EmptyToken())
  })

  val myRoute: Route = (publicRoutes ++ sessionRoutes).reduce(_ ~ _)
}


//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// In-memory session managements @todo replace with something less naive.
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/**
  * @todo replace this with an existing library that does The Right Things
  * @todo do we want to enforce timeouts as well?
  */
object SessionManager {
  type Session = scala.collection.mutable.Map[String, Any]

  private var sessionMap : Map[String, (UserPOJO, Date)] = Map() //Session tokens -> usernames
  private var sessions: Map[String, Session] = Map()

  def token(key: String): SessionToken = sessionMap.get(key) match {
    case Some((user, timeout)) =>
      if (new Date().before(timeout)) {
        //@HACK need better way of mapping user levels to tokens
        if (user.level == 0 || user.level == 1) ReadWriteToken(key, user.userName)
        else if (user.level == 3) ReadonlyToken(key, user.userName)
        else ???
      } else {
        remove(key)
        NewlyExpiredToken(key)
      }
    case None => EmptyToken()
  }

  def add(user: UserPOJO): String = {
    val sessionToken = generateToken() //@todo generate a proper key.
    sessionMap += sessionToken -> (user, timeoutDate)
    sessions += sessionToken -> scala.collection.mutable.Map()
    sessionToken
  }

  def session(token: SessionToken): Session = token match {
    case ut: UserToken => sessions(ut.token)
    case _ => scala.collection.mutable.Map()
  }

  def remove(key: String): Unit = {
    sessionMap -= key
    sessions -= key
  }

  private def timeoutDate : Date = {
    val c = Calendar.getInstance()
    c.add(Calendar.DATE, 7)
    c.getTime
  }

  private def generateToken(): String = {
    val random: SecureRandom = new SecureRandom()
    val bytes = Array[Byte](20)
    random.nextBytes(bytes)
    val candidate = bytes.toString
    if (sessionMap.contains(candidate)) generateToken()
    else candidate
  }
}

/** @note a custom Option so that Scala doesn't use None as an implicit parameter. */
trait SessionToken {
  def isLoggedIn: Boolean = this.isInstanceOf[UserToken]

  def belongsTo(uname: String): Boolean = this match {
    case ut: UserToken => ut.username == uname
    case _: EmptyToken => false
  }

  def tokenString: String = this match {
    case ut: UserToken => ut.token
    case NewlyExpiredToken(t) => t
    case _ => ""
  }
}
abstract class UserToken(val token: String, val username: String) extends SessionToken
case class NewlyExpiredToken(token: String) extends SessionToken
case class ReadWriteToken(override val token: String, override val username: String) extends UserToken(token, username)
case class ReadonlyToken(override val token: String, override val username: String) extends UserToken(token, username)
case class EmptyToken() extends SessionToken
