/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.hydra

import java.security.SecureRandom
import java.util.{Calendar, Date}

import akka.http.scaladsl.model.{Multipart, StatusCodes}
import akka.http.scaladsl.server.{ExceptionHandler, Route, StandardRoute}
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser.ArchiveParser
import spray.json._
import akka.http.scaladsl.marshalling.ToResponseMarshallable
import edu.cmu.cs.ls.keymaerax.{Configuration, Logging}
import edu.cmu.cs.ls.keymaerax.core.Formula
import akka.http.scaladsl.model.Multipart.FormData.BodyPart
import akka.http.scaladsl.server.Directives._
import akka.http.scaladsl.model.headers._
import akka.http.scaladsl.model.headers.CacheDirectives.`max-age`
import akka.http.scaladsl.model.headers.CacheDirectives.`no-cache`
import akka.http.scaladsl.model.StatusCodes._
import edu.cmu.cs.ls.keymaerax.infrastruct.Position

import scala.annotation.tailrec
import scala.language.postfixOps

/**
 * RestApi is the API router. See README.md for a description of the API.
 */
object RestApi extends Logging {
  //region Database setup

  private val database = DBAbstractionObj.defaultDatabase //SQLite //Not sure when or where to create this... (should be part of Boot?)

  val catchAllExceptionHandler = ExceptionHandler {
    case ex: Exception =>
      extractUri { uri =>
        val errorJson: String = new ErrorResponse(ex.getMessage, ex).getJson.prettyPrint
        logger.error(s"Request '$uri' resulted in uncaught exception", ex)
        complete(StatusCodes.InternalServerError, errorJson)
      }
  }

  //endregion

  //region Constants for accessing resources and database values.

  private val DEFAULT_ARCHIVE_LOCATION = "http://keymaerax.org/KeYmaeraX-projects/"
  private val BUNDLED_ARCHIVE_DIR = "/keymaerax-projects/"
  private val BUNDLED_ARCHIVE_LOCATION = s"classpath:$BUNDLED_ARCHIVE_DIR"

  //endregion

  //region Helper Methods

  private def getUserFromUserIdCookieContent(userIdContent : String):String = userIdContent //for now...

  private def getFileContentsFromFormData(item : Multipart.FormData.BodyPart) : String = {
    val entity = item.entity
    val headers = item.headers
    val content = item.entity.getDataBytes().toString() //@todo not sure if this is correct.

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
    respondWithHeader(`Cache-Control`(scala.collection.immutable.Seq(`no-cache`, `max-age`(0)))) {
      complete(response)
    }

  def completeRequest(r: Request, t: SessionToken): StandardRoute = t match {
    case NewlyExpiredToken(_) =>
      assert(!Configuration.getString(Configuration.Keys.USE_DEFAULT_USER).contains("true"), "Default user is not supposed to expire, but did.")
      complete(Unauthorized, Nil, s"Session $t expired")
    case _ =>
      if (r.permission(t)) complete(standardCompletion(r, t))
      else if (Configuration.getString(Configuration.Keys.USE_DEFAULT_USER).contains("true")) complete(completeResponse(new ErrorResponse("Unexpected internal error: default user lacks permission; please reconfigure keymaerax.conf to USE_DEFAULT_USER=ask, restart KeYmaera X, and register an ordinary local login name.") :: Nil))
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
      case e: ErrorResponse => logger.warn("Error response details: " + e.msg, e.exn)
      case _ => /* nothing to do */
    })

    try {
      responses match {
        case hd :: Nil => hd.print
        case _ => JsArray(responses.map(_.getJson): _*).compactPrint
      }
    } catch {
      case ex: Throwable =>
        ex.printStackTrace()
        new ErrorResponse("Error serializing response", ex).print
    }
  }

  //endregion

  //region Common partial routes

  private val userPrefix = pathPrefix("user" / Segment)

  private val denied = path("private" / "KeyStore.jks") { get { getFromResource("index_bootstrap.html") } }

  //The static directory.
  private val staticRoute =
    pathPrefix("") { get {
      respondWithHeader(`Cache-Control`(scala.collection.immutable.Seq(`no-cache`, `max-age`(0)))) {
        getFromResourceDirectory("")
      }
    }}
  private val homePage = path("") { get {
    respondWithHeader(`Cache-Control`(scala.collection.immutable.Seq(`no-cache`, `max-age`(0)))) {
      if (!HyDRAServerConfig.isHosted) {
        // on non-hosted instance: offer default login feature
        if (Configuration.getString(Configuration.Keys.USE_DEFAULT_USER).contains("true")) {
          Configuration.getString(Configuration.Keys.DEFAULT_USER) match {
            case Some(userName) => database.getUser(userName) match {
              case Some(user) =>
                // login default user and show models
                SessionManager.defaultUserTokenKey = Some(SessionManager.add(user))
                getFromResource("index_localhost.html") //@note auto-forwards to models
              case _ =>
                // database does not know default user: first time use by a user with a fresh database, show license and
                // ask for preferred user mode
                getFromResource("index_localhost.html")
            }
            // default user not set (this should not happen, but if it does): show login page
            case _ => getFromResource("index_bootstrap.html")
          }
        } else if (Configuration.getString(Configuration.Keys.USE_DEFAULT_USER).contains("false")) {
          // user opted out of localhost default login, show login page
          getFromResource("index_bootstrap.html")
        } else if (Configuration.getString(Configuration.Keys.USE_DEFAULT_USER).contains("ask")) {
          // first time use by a user with a prior installation without default user feature
          getFromResource("index_bootstrap.html")
        } else getFromResource("index_bootstrap.html")
      } else getFromResource("index_bootstrap.html")
    }
  }}

  //endregion

  //region Users

  val users: Route = pathPrefix("user" / Segment / Segment / "mode" / Segment) { (username, password, mode) => {
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

  val defaultLogin: Route = pathPrefix("user" / Segment / Segment / "defaultLogin") { (username, password) => {
    pathEnd {
      get {
        val request = new LocalLoginRequest(database,username, password)
        completeRequest(request, EmptyToken())
      }
    }
  }}

  val setDefaultUser: Route = pathPrefix("user" / Segment / Segment / "setDefaultUser" / Segment) { (username, password, useDefault) => {
    pathEnd {
      post {
        val request = new SetDefaultUserRequest(database, username, password, useDefault == "true")
        completeRequest(request, EmptyToken())
      }
    }
  }}

  val logoff: SessionToken=>Route  = (t: SessionToken) => path("user" / "logoff") { pathEnd { get {
    t match {
      case ut: UserToken =>
        SessionManager.defaultUserTokenKey = None
        SessionManager.remove(ut.token)
      case NewlyExpiredToken(_) => //Well, that was convienant.
      case _ => //that works too.
    }
    complete("[]")
  }}}

  //endregion

  //region Models

  // FYI to get cookies do this:
  val cookie_echo: Route = pathPrefix("cookie_echo" / Segment) { cookieName => cookie(cookieName) { cookieValue => {
    complete(cookieName + ": " + cookieValue.value)
  }}}

  val userTheme: SessionToken=>Route = (t: SessionToken) => path("users" / Segment / "theme") { userId => pathEnd {
    get {
      val request = new GetUserThemeRequest(database, userId)
      completeRequest(request, t)
    } ~
      post {
        entity(as[String]) { themeStr => {
          def convert(k: String, v: JsValue): (String, String) = k match {
            case "renderMargins" => v match {
              case _: JsArray => k -> v.toString()
              case o: JsObject if Set("0","1").subsetOf(o.fields.keySet) => k -> JsArray(o.fields("0"), o.fields("1")).toString
              case _ => throw new IllegalArgumentException("Render margins must be either an array of numbers or an object {'0': JsNumber, '1': JsNumber}, but got " + v.toString)
            }
            case _ => k -> v.toString()
          }

          val theme = themeStr.parseJson.asJsObject.fields.map({case (k,v) => convert(k, v)})
          val request = new SetUserThemeRequest(database, userId, theme("css"), theme("fontSize"), theme("renderMargins"))
          completeRequest(request, t)
        }}}
  }}

  // GET /models/user returns a list of all models belonging to this user. The cookie must be set.
  val modelList: SessionToken=>Route = (t : SessionToken) => pathPrefix("models" / "users" / Segment / Segment.?) {(userId, folder) => { pathEnd { get {
    val request = new GetModelListRequest(database, userId, folder)
    completeRequest(request, t)
  }}}}

  val userModel: SessionToken=>Route = (t : SessionToken) => userPrefix {userId => {pathPrefix("model" / Segment) {modelNameOrId => {pathEnd {
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

  val importExampleRepo: SessionToken=>Route = (t: SessionToken) => path("models" / "users" / Segment / "importRepo") { userId => { pathEnd {
    post {
      entity(as[String]) { repoUrl => {
        try {
          val content = DatabasePopulator.loadResource(repoUrl)
          val r = new UploadArchiveRequest(database, userId, content, None)
          completeRequest(r, t)
        } catch {
          case ex: java.net.UnknownHostException => complete(completeResponse(new ErrorResponse("Example repository is unreachable, please check that your computer is online.", ex) :: Nil))
        }

      }}
    }
  }}}

  val deleteModel: SessionToken=>Route = (t : SessionToken) => userPrefix {userId => pathPrefix("model" / Segment / "delete") { modelId => pathEnd {
    post {
      val r = new DeleteModelRequest(database, userId, modelId)
      completeRequest(r, t)
    }
  }}}

  val deleteModelProofSteps: SessionToken=>Route = (t : SessionToken) => userPrefix {userId => pathPrefix("model" / Segment / "deleteProofSteps") { modelId => pathEnd {
    post {
      val r = new DeleteModelProofStepsRequest(database, userId, modelId)
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
  val userModel2: SessionToken=>Route = (t : SessionToken) => userPrefix {userId => {pathPrefix("modelupload" / Segment.?) { modelNameOrId =>
  {pathEnd {
    post {
      entity(as[String]) { contents => {
        val request = new UploadArchiveRequest(database, userId, contents, modelNameOrId)
        completeRequest(request, t)
      }}}}}}}}

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

  /** Extracts and stores a tactic from the recorded proof steps. */
  val extractTactic: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "extract" / Map("verbose" -> true, "succinct" -> false)) { (userName, proofId, verbose) => { pathEnd {
    get {
      val request = new ExtractTacticRequest(database, userName, proofId, verbose)
      completeRequest(request, t)
    }
  }}}

  /** Reads a previously extracted tactic. */
  val getTactic: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "tactic") { (userName, proofId) => { pathEnd {
    get {
      val request = new GetTacticRequest(database, userName, proofId)
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

  val deleteAllModels: SessionToken=>Route = (t : SessionToken) => path("models" / "user" / Segment / "delete" / "all") { userId => { pathEnd {
    get {
      //@note potential performance bottleneck: loads all models just to get ids
      val request = new DeleteAllModelsRequest(database, userId)
      completeRequest(request, t)
    }
  }}}

  val createTemplate: SessionToken=>Route = (t : SessionToken) => pathPrefix("models" / "users" / Segment / "templates" / Segment / "create") {(userId, template) => { pathEnd { post {
    entity(as[String]) { x => {
      val obj = x.parseJson.asJsObject
      val code = obj.fields("code").asInstanceOf[JsString].value
      val vertices = obj.fields("vertices").asInstanceOf[JsArray]
      val edges = obj.fields("edges").asInstanceOf[JsArray]
      val request = template match {
        case "controlledstability" => new CreateControlledStabilityTemplateRequest(userId, code, vertices, edges)
      }
      completeRequest(request, t)
    }}
  }}}}

  //endregion

  //region Proofs

    val createProof: SessionToken=>Route = (t: SessionToken) => path("models" / "users" / Segment / "model" / Segment / "createProof") { (userId, modelId) => { pathEnd {
      post {
        entity(as[String]) { x => {
          val obj = x.parseJson
          val submittedProofName = obj.asJsObject.getFields("proofName").last.asInstanceOf[JsString].value
          val proofDescription = obj.asJsObject.getFields("proofDescription").last.asInstanceOf[JsString].value
          val request = new CreateProofRequest(database, userId, modelId, submittedProofName, proofDescription)
          completeRequest(request, t)
        }}
      }
    }}}

    val openOrCreateLemmaProof: SessionToken=>Route = (t: SessionToken) => path("models" / "users" / Segment / "model" / Segment / "openOrCreateLemmaProof") { (userId, modelName) => { pathEnd {
      post {
        entity(as[String]) { x => {
          val obj = x.parseJson
          val parentProofId = obj.asJsObject.getFields("parentProofId").last.asInstanceOf[JsString].value
          val parentTaskId = obj.asJsObject.getFields("parentTaskId").last.asInstanceOf[JsString].value

          val request = new OpenOrCreateLemmaProofRequest(database, userId, modelName, parentProofId, parentTaskId)
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

    val proofList: SessionToken=>Route = (t: SessionToken) => path("proofs" / "users" / Segment) { (userId) => { pathEnd {
      get {
        val request = new ProofsForUserRequest(database, userId)
        completeRequest(request, t)
      }
    }}}

    val userLemmas: SessionToken=>Route = (t: SessionToken) => path("lemmas" / "users" / Segment) { userId => { pathEnd {
      get {
        val request = new UserLemmasRequest(database, userId)
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

    val getProofLemmas: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "usedLemmas") { (userId, proofId) => { pathEnd {
      get {
        val request = new GetProofLemmasRequest(database, userId, proofId)
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

    val proofTasksNode: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "node") { (userId, proofId, nodeId) => { pathEnd {
      get {
        val request = new ProofTaskNodeRequest(database, userId, proofId, nodeId)
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
        parameters('strict.as[Boolean]) { strict =>
          val request = new ProofTaskExpandRequest(database, userId, proofId, nodeId, strict)
          completeRequest(request, t)
        }
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
      val positionStringParts = id.split(',').toList
      val (idx :: inExprs) = positionStringParts.map(str =>
        try {
          str.toInt
        } catch {
          case e: NumberFormatException => {
            //HACK: if position is top-level (no inExpr) and unspecified, then "Hint" web ui was probably used. In this case, assume top-level succ.
            //@todo This is a hack that *should* be fixed in the front-end by telling the "Hint: ...|...|...|" portion of the web ui to please specify a position. See sequent.js and collapsiblesequent.html
            if(str.equals("null") && positionStringParts.length==1)
              1
            else
              throw new Exception("Invalid formulaId " + str + " when parsing positions")
          }
        }
      )

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

    val definitionsList: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment/ "listDefinitions") { (userId, proofId, nodeId) => { pathEnd {
      get {
        val request = new GetApplicableDefinitionsRequest(database, userId, proofId, nodeId)
        completeRequest(request, t)
      }
    }}}

    val setDefinition: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "definitions") { (userId, proofId) => { pathEnd {
      post {
        entity(as[String]) { params => {
          val (what: JsString) :: (repl: JsString) :: Nil = JsonParser(params).asJsObject.getFields("what", "repl").toList
          val request = new SetDefinitionsRequest(database, userId, proofId, what.value, repl.value)
          completeRequest(request, t)
        }}
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

    val derivationInfo: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "derivationInfos" / Segment.?) { (userId, proofId, nodeId, axiomId) => { pathEnd {
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
      post {
        entity(as[String]) { params =>
          val (pName: JsString) :: (pType: JsString) :: (pValue: JsString) :: Nil =
            JsonParser(params).asJsObject.getFields("param", "type", "value").toList
          completeRequest(new CheckTacticInputRequest(database, userId, proofId, nodeId, tacticId, pName.value, pType.value, pValue.value), t)
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
            paramInfo.isEmpty ||
              (paramInfo match { case Some(_: OptionArg) => false case _ => obj.getFields("value").isEmpty})
          })
          if (illFormedParams.isEmpty) {
            val inputs = paramArray.map({ obj =>
              val paramName = obj.getFields("param").head.asInstanceOf[JsString].value
              expectedInputs.find(_.name == paramName) match {
                case Some(OptionArg(paramInfo)) => obj.getFields("value").headOption match {
                  case Some(JsString(paramValue)) => Some(BelleTermInput(paramValue, Some(paramInfo)))
                  case _ => None
                }
                case paramInfo =>
                  val paramValue = obj.getFields("value").head.asInstanceOf[JsString].value
                  Some(BelleTermInput(paramValue, paramInfo))
              }
            }).filter(_.isDefined).map(_.get)
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
              val (paramName: JsString) :: (paramValue: JsString) :: Nil = obj.getFields("param", "value").toList
              val paramInfo = expectedInputs.find(_.name == paramName.value)
              BelleTermInput(paramValue.value, paramInfo)
            })
          val request = new RunBelleTermRequest(database, userId, proofId, nodeId, tacticId, None, None, inputs.toList, consultAxiomInfo=true, stepwise=stepwise)
          completeRequest(request, t)
        }
        }}}
    }}}

    val doCustomTactic: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "doCustomTactic") { (userId, proofId, nodeId) => { pathEnd {
      post { parameters('stepwise.as[Boolean]) { stepwise =>
        entity(as[String]) { tactic => {
          val request = new RunBelleTermRequest(database, userId, proofId, nodeId, tactic.trim.stripPrefix(";"), None, consultAxiomInfo=false, stepwise=stepwise)
          completeRequest(request, t)
        }}
      }}}
    }}

    val doSearch: SessionToken=>Route = (t: SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "doSearch" / Segment / Segment) { (userId, proofId, goalId, where, tacticId) => { pathEnd {
      get { parameters('stepwise.as[Boolean]) { stepwise =>
        val pos = where match {
          case "R" => Find.FindRFirst
          case "L" => Find.FindLFirst
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
            case "R" => Find.FindRFirst
            case "L" => Find.FindLFirst
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

    val undoLastProofStep: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / "undoLastStep") { (userId, proofId) => { pathEnd {
      get {
        val request = new UndoLastProofStepRequest(database, userId, proofId)
        completeRequest(request, t)
      }
    }}}

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
        get { parameters(('assumptions.as[String], 'fmlIndices.as[String])) { (assumptions: String, fmlIndices: String) =>
          val request = new CounterExampleRequest(database, userId, proofId, nodeId, assumptions, fmlIndices)
          completeRequest(request, t)
        }}
      }}
    }

    val odeConditions: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "odeConditions") { (userId, proofId, nodeId) => {
      pathEnd {
        get {
          val request = new ODEConditionsRequest(database, userId, proofId, nodeId)
          completeRequest(request, t)
        }
      }}
    }

    val pegasusCandidates: SessionToken=>Route = (t : SessionToken) => path("proofs" / "user" / Segment / Segment / Segment / "pegasusCandidates") { (userId, proofId, nodeId) => {
      pathEnd {
        get {
          val request = new PegasusCandidatesRequest(database, userId, proofId, nodeId)
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

  //endregion

  //region Archives

  val guestBrowseArchiveRequest: Route = path("show" / Segments) { archiveUri => pathEnd {
    get {
      val (archiveLocation: String, archiveRelativeLocation: String) = archiveUri match {
        case head::Nil if head.startsWith("http") || head.startsWith("https") => (head, head)
        case segments =>
          val path = segments.reduce(_+"/"+_)
          if (getClass.getResourceAsStream(BUNDLED_ARCHIVE_DIR + path) != null) (BUNDLED_ARCHIVE_LOCATION + path, path)
          else {
            logger.info(s"Could not find ${BUNDLED_ARCHIVE_LOCATION + path} resource in JAR file. Accessing remote host.")
            (DEFAULT_ARCHIVE_LOCATION + path, path)
          }
      }
      val request = new OpenGuestArchiveRequest(database, archiveLocation, archiveRelativeLocation)
      completeRequest(request, EmptyToken())
    }
  }}

  //endregion

  //region Configuration and versioning information

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

  val wolframEngineConfSuggestion: Route = path("config" / "wolframengine" / "suggest") {
    pathEnd {
      get {
        val request = new GetWolframEngineConfigSuggestionRequest(database)
        completeRequest(request, EmptyToken())
      }
    }
  }

  val wolframScriptConfSuggestion: Route = path("config" / "wolframscript" / "suggest") {
    pathEnd {
      get {
        val request = new GetWolframScriptConfigSuggestionRequest(database)
        completeRequest(request, EmptyToken())
      }
    }
  }

  val z3ConfSuggestion: Route = path("config" / "z3" / "suggest") {
    pathEnd {
      get {
        completeRequest(new GetZ3ConfigSuggestionRequest(), EmptyToken())
      }
    }
  }

  val tool: Route = path("config" / "tool") {
    pathEnd {
      get {
        Configuration(Configuration.Keys.QE_TOOL) match {
          case "mathematica" => completeRequest(new MathematicaConfigStatusRequest(database), EmptyToken())
          case "wolframengine" => completeRequest(new WolframEngineConfigStatusRequest(database), EmptyToken())
          case "wolframscript" => completeRequest(new WolframScriptConfigStatusRequest(database), EmptyToken())
          case "z3" => completeRequest(new Z3ConfigStatusRequest(database), EmptyToken())
        }
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
          val request = new GetMathematicaConfigurationRequest(database, "mathematica")
          completeRequest(request, EmptyToken())
      } ~
      post {
        entity(as[String]) { params => {
          val p = JsonParser(params).asJsObject.fields.map(param => param._1.toString -> param._2.asInstanceOf[JsString].value)
          assert(p.contains("linkName"), "linkName not in: " + p.keys.toString())
          assert(p.contains("jlinkLibDir"), "jlinkLibDir not in: " + p.keys.toString()) //@todo These are schema violations and should be checked as such, but I needed to disable the validator.
          assert(p.contains("jlinkTcpip"), "jlinkTcpip not in: " + p.keys.toString())
          val linkName: String = p("linkName")
          val jlinkLibDir: String = p("jlinkLibDir")
          val jlinkTcpip: String = p("jlinkTcpip")
          val request = new ConfigureMathematicaRequest(database, "mathematica", linkName, jlinkLibDir, jlinkTcpip)
          completeRequest(request, EmptyToken())
        }}
      }
    }
  }

  val wolframEngineConfig: Route = path("config" / "wolframengine") {
    pathEnd {
      get {
        val request = new GetMathematicaConfigurationRequest(database, "wolframengine")
        completeRequest(request, EmptyToken())
      } ~
        post {
          entity(as[String]) { params => {
            val p = JsonParser(params).asJsObject.fields.map(param => param._1.toString -> param._2.asInstanceOf[JsString].value)
            assert(p.contains("linkName"), "linkName not in: " + p.keys.toString())
            assert(p.contains("jlinkLibDir"), "jlinkLibDir not in: " + p.keys.toString()) //@todo These are schema violations and should be checked as such, but I needed to disable the validator.
            assert(p.contains("jlinkTcpip"), "jlinkTcpip not in: " + p.keys.toString())
            val linkName: String = p("linkName")
            val jlinkLibDir: String = p("jlinkLibDir")
            val jlinkTcpip: String = p("jlinkTcpip")
            val request = new ConfigureMathematicaRequest(database, "wolframengine", linkName, jlinkLibDir, jlinkTcpip)
            completeRequest(request, EmptyToken())
          }}
        }
    }
  }

  val z3Config: Route = path("config" / "z3") {
    pathEnd {
      get {
        completeRequest(new GetZ3ConfigurationRequest(), EmptyToken())
      } ~
      post {
        entity(as[String]) { params => {
          val p = JsonParser(params).asJsObject.fields.map(param => param._1 -> param._2.asInstanceOf[JsString].value)
          assert(p.contains("z3Path"), "z3 path not in: " + p.keys.toString())
          val z3Path: String = p("z3Path")
          completeRequest(new ConfigureZ3Request(z3Path), EmptyToken())
        }}
      }
    }
  }

  val fullConfig: Route = path("config" / "fullContent") {
    pathEnd {
      get {
        completeRequest(new GetFullConfigRequest(), EmptyToken())
      } ~
      post {
        entity(as[String]) { params => {
          val content = params.parseJson.asJsObject.fields("content") match { case JsString(s) => s }
          completeRequest(new SaveFullConfigRequest(content), EmptyToken())
        }}
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

  //endregion

  // region Tools

  val toolStatus: Route = path("tools" / "vitalSigns") {
    pathEnd {
      get {
        completeRequest(new ToolStatusRequest(database, Configuration(Configuration.Keys.QE_TOOL)), EmptyToken())
      }
    }
  }

  val cancelTool: Route = path("tools" / "cancel") {
    pathEnd {
      get {
        completeRequest(new CancelToolRequest(), EmptyToken())
      }
    }
  }

  val restartTool: Route = path("tools" / "restart") {
    pathEnd {
      get {
        completeRequest(new RestartToolRequest(database, Configuration(Configuration.Keys.QE_TOOL)), EmptyToken())
      }
    }
  }

  val testToolConnection: Route = path("tools" / "testConnection") {
    pathEnd {
      get {
        completeRequest(new TestToolConnectionRequest(database, Configuration(Configuration.Keys.QE_TOOL)), EmptyToken())
      }
    }
  }

  // endregion

  //region Examples

  val examples: SessionToken=>Route = (t : SessionToken) => path("examples" / "user" / Segment / "all") { userId =>
    pathEnd {
      get {
        val request = new ListExamplesRequest(database, userId)
        completeRequest(request, t)
      }
    }
  }

  val templates: SessionToken=>Route = (t : SessionToken) => path("templates" / "user" / Segment / "all") { userId =>
    pathEnd {
      get {
        val request = new GetTemplatesRequest(database, userId)
        completeRequest(request, t)
      }
    }
  }

  //endregion

  //region More proof development stuff

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

  //endregion

  //region Special developer actions

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

  //endregion

  //region Proof validation

  /** Validates the proof of a lemma. */
  val validateProof: Route = path("validate") { pathEnd {
    post {
      entity(as[String]) { archiveFileContents => {
        val entries = ArchiveParser.parse(archiveFileContents)

        if(entries.length != 1)
          complete(completeResponse(new ErrorResponse(s"Expected exactly one model in the archive but found ${entries.length}") :: Nil))
        else if(entries.head.tactics.length != 1)
          complete(completeResponse(new ErrorResponse(s"Expected exactly one proof in the archive but found ${entries.head.tactics.length} proofs. Make sure you export from the Proofs page, not the Models page.") :: Nil))
        else {
          val entry = entries.head
          val model = entry.model.asInstanceOf[Formula]
          val tactic = entry.tactics.head._3
          complete(standardCompletion(new ValidateProofRequest(database, model, tactic, entry.defs), EmptyToken()))
        }
      }}
    }
  }}

  val checkProofValidation: Route = path("validate" / Segment) { (taskId) => {
    get {
      complete(standardCompletion(new CheckValidationRequest(database, taskId), EmptyToken()))
    }
  }}

  //endregion

  //region LOCAL server management

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

  //endregion

  //region routing

  val publicRoutes: List[Route] =
    denied ::
    staticRoute        ::
    homePage           ::
    isLocal            ::
    extractdb          ::
    shutdown           ::
    users              ::
    defaultLogin       ::
    setDefaultUser     ::
    cookie_echo        ::
    kyxConfig          ::
    keymaeraXVersion   ::
    mathematicaConfig  ::
    wolframEngineConfig ::
    z3Config           ::
    toolStatus         ::
    tool               ::
    guestBrowseArchiveRequest ::
    systemInfo         ::
    fullConfig         ::
    mathConfSuggestion ::
    wolframEngineConfSuggestion ::
    wolframScriptConfSuggestion::
    z3ConfSuggestion   ::
    devAction          ::
    checkProofValidation ::
    validateProof      ::
    licenses           ::
    restartTool        ::
    cancelTool         ::
    testToolConnection ::
    Nil

  /** Requests that need a session token parameter.
    *
    * @see [[sessionRoutes]] is built by wrapping all of these sessions in a cookieOptional("session") {...} that extrtacts the cookie name. */
  private val partialSessionRoutes : List[SessionToken => Route] =
    downloadAllModels     :: //@note before userModel2 to match correctly
    modelList             ::
    modelTactic           ::
    userModel             ::
    userModel2            ::
    deleteModel           ::
    createProof           ::
    openOrCreateLemmaProof ::
    createModelTacticProof::
    initProofFromTactic   ::
    getProofLemmas        ::
    importExampleRepo     ::
    deleteProof           ::
    proofListForModel     ::
    proofList             ::
    downloadAllProofs     :: //@note before openProof to match correctly
    downloadModelProofs   ::
    openProof             ::
    changeProofName       ::
    proofProgressStatus   ::
    proofCheckIsProved    ::
    proofTasksNew         ::
    proofTasksNode        ::
    proofTasksParent      ::
    proofTasksPathAll     ::
    proofTasksBranchRoot  ::
    proofTaskExpand       ::
    proofNodeSequent      ::
    axiomList             ::
    sequentList           ::
    definitionsList       ::
    setDefinition         ::
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
    getTactic             ::
    tacticDiff            ::
    extractLemma          ::
    downloadProblemSolution ::
    counterExample        ::
    odeConditions         ::
    pegasusCandidates     ::
    setupSimulation       ::
    simulate              ::
    pruneBelow            ::
    undoLastProofStep     ::
    modelplex             ::
    exportSequent         ::
    testSynthesis         ::
    examples              ::
    templates             ::
    createTemplate        ::
    stepwiseTrace         ::
    updateUserModel       ::
    userTheme             ::
    browseProofRoot       ::
    browseNodeChildren    ::
    deleteModelProofSteps ::
    deleteAllModels       ::
    userLemmas            ::
    logoff                ::
    // DO NOT ADD ANYTHING AFTER LOGOFF!
    Nil

  val sessionRoutes: List[Route] = partialSessionRoutes.map(routeForSession => optionalHeaderValueByName("x-session-token") {
    case Some(token) if  HyDRAServerConfig.isHosted => routeForSession(SessionManager.token(token))
    case Some(token) if !HyDRAServerConfig.isHosted => routeForSession(SessionManager.token(SessionManager.defaultUserTokenKey.getOrElse(token)))
    case None if  HyDRAServerConfig.isHosted => routeForSession(EmptyToken())
    case None if !HyDRAServerConfig.isHosted => routeForSession(SessionManager.defaultUserTokenKey.map(SessionManager.token).getOrElse(EmptyToken()))
  })

  val api: Route = handleExceptions(catchAllExceptionHandler)((publicRoutes ++ sessionRoutes).reduce(_ ~ _))

  //endregion
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// Custom and stand-alone in-memory session managements @todo replace with something less naive.
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/**
  * @todo replace this with an existing library that does The Right Things
  * @todo do we want to enforce timeouts as well?
  */
object SessionManager {
  type Session = scala.collection.mutable.Map[String, Any]

  private var sessionMap : Map[String, (UserPOJO, Date)] = Map() //Session tokens -> usernames
  private var sessions: Map[String, Session] = Map()
  private[hydra] var defaultUserTokenKey: Option[String] = None

  def token(key: String): SessionToken = sessionMap.get(key) match {
    case Some((user, timeout)) =>
      if (new Date().before(timeout)) {
        createToken(key, user)
      } else {
        remove(key)
        // on local host, recreate default user token
        if (Configuration.getString(Configuration.Keys.USE_DEFAULT_USER).contains("true") &&
          Configuration.contains(Configuration.Keys.DEFAULT_USER)) {
          createToken(key, user)
        } else NewlyExpiredToken(key)
      }
    case None => EmptyToken()
  }

  /** Creates a token with token `key` representing `user`. */
  private[this] def createToken(key: String, user: UserPOJO): SessionToken = {
    //@HACK need better way of mapping user levels to tokens
    if (user.level == 0 || user.level == 1) ReadWriteToken(key, user.userName)
    else if (user.level == 3) ReadonlyToken(key, user.userName)
    else ???
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
    val expiresIn =
      // local user: sessions don't expire
      if (Configuration.getString(Configuration.Keys.USE_DEFAULT_USER).contains("true") &&
        Configuration.contains(Configuration.Keys.DEFAULT_USER)) {
        Int.MaxValue
      } else 7
    c.add(Calendar.DATE, expiresIn)
    c.getTime
  }

  @tailrec
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
