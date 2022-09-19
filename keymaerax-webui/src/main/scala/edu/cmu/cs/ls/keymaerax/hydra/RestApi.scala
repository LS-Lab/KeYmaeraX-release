/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.hydra

import akka.http.scaladsl.model.StatusCodes
import akka.http.scaladsl.server.{Directive, ExceptionHandler, Route, StandardRoute}
import spray.json._
import akka.http.scaladsl.marshalling.ToResponseMarshallable
import edu.cmu.cs.ls.keymaerax.{Configuration, Logging}
import akka.http.scaladsl.server.Directives._
import akka.http.scaladsl.model.headers._
import akka.http.scaladsl.model.headers.CacheDirectives.`max-age`
import akka.http.scaladsl.model.headers.CacheDirectives.`no-cache`
import akka.http.scaladsl.model.StatusCodes._
import edu.cmu.cs.ls.keymaerax.hydra.restapi.Configuration._
import edu.cmu.cs.ls.keymaerax.hydra.restapi.Models._
import edu.cmu.cs.ls.keymaerax.hydra.restapi.ModelPlex._
import edu.cmu.cs.ls.keymaerax.hydra.restapi.Proofs._
import edu.cmu.cs.ls.keymaerax.hydra.restapi.Tools._
import edu.cmu.cs.ls.keymaerax.hydra.restapi.Users._

import scala.language.postfixOps

/**
 * RestApi is the API router. See README.md for a description of the API.
 */
object RestApi extends Logging {
  val database: SQLite.SQLiteDB  = DBAbstractionObj.defaultDatabase //SQLite //Not sure when or where to create this... (should be part of Boot?)

  private val catchAllExceptionHandler = ExceptionHandler {
    case ex: Exception =>
      extractUri { uri =>
        val errorJson: String = new ErrorResponse(ex.getMessage, ex).getJson.prettyPrint
        logger.error(s"Request '$uri' resulted in uncaught exception", ex)
        complete(StatusCodes.InternalServerError, errorJson)
      }
  }

  //region Helper Methods

  def completeRequest(r: Request, t: SessionToken): StandardRoute = t match {
    case NewlyExpiredToken(_) =>
      assert(!Configuration.getString(Configuration.Keys.USE_DEFAULT_USER).contains("true"), "Default user is not supposed to expire, but did.")
      complete(Unauthorized, Nil, s"Session $t expired")
    case _ =>
      if (r.permission(t)) complete(standardCompletion(r, t))
      else if (Configuration.getString(Configuration.Keys.USE_DEFAULT_USER).contains("true")) complete(completeResponse(
        new ErrorResponse("KeYmaera X may have restarted or may not have finished starting yet; please try to refresh the page (may need to refresh several times). If the error persists, try to reconfigure keymaerax.conf to USE_DEFAULT_USER=ask, restart KeYmaera X, and register a local login name.") :: Nil))
      else complete(Forbidden, Nil, s"Permission to this resource (${r.getClass.getCanonicalName}) is denied for session $t")
  }

  def standardCompletion(r: Request, t: SessionToken): ToResponseMarshallable = t match {
    case NewlyExpiredToken(_) => throw new AssertionError("Expired tokens are not standard request completions, use completeRequest instead")
    case _ =>
      val responses = r.getResultingResponses(t)
      completeResponse(responses)
  }

  /** @note you probably don't actually want to use this. Use standardCompletion instead. */
  def completeResponse(responses: List[Response]): ToResponseMarshallable  = {
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
        new ErrorResponse("Error generating response: " + ex.getMessage, ex).print
    }
  }

  //endregion

  val userPrefix: Directive[Tuple1[String]] = pathPrefix("user" / Segment)

  val denied: Route = path("private" / "KeyStore.jks") {
    get {
      getFromResource("index_bootstrap.html")
    }
  }

  val staticRoute: Route = pathPrefix("") {
    get {
      respondWithHeader(`Cache-Control`(scala.collection.immutable.Seq(`no-cache`, `max-age`(0)))) {
        getFromResourceDirectory("")
      }
    }
  }

  val homePage: Route = path("") {
    get {
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
    }
  }

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
    checkProofValidation ::
    validateProof      ::
    licenses           ::
    restartTool        ::
    cancelTool         ::
    testToolConnection ::
    hotkeys            ::
    Nil

  /** Requests that need a session token parameter.
    *
    * @see [[sessionRoutes]] is built by wrapping all of these sessions in a cookieOptional("session") {...} that extrtacts the cookie name. */
  private val partialSessionRoutes: List[SessionToken => Route] =
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
