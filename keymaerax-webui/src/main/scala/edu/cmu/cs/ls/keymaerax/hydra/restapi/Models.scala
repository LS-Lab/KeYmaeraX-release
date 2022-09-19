/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.hydra.restapi

import akka.http.scaladsl.server.Route
import spray.json._
import spray.json.DefaultJsonProtocol._
import akka.http.scaladsl.server.Directives._
import edu.cmu.cs.ls.keymaerax.Logging
import edu.cmu.cs.ls.keymaerax.hydra.RestApi.{completeRequest, completeResponse, database, userPrefix}
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.hydra.requests.models._
import edu.cmu.cs.ls.keymaerax.hydra.requests.proofs.ExtractModelSolutionsRequest

import scala.language.postfixOps

object Models extends Logging {

  private val DEFAULT_ARCHIVE_LOCATION = "http://keymaerax.org/KeYmaeraX-projects/"
  private val BUNDLED_ARCHIVE_DIR = "/keymaerax-projects/"
  private val BUNDLED_ARCHIVE_LOCATION = s"classpath:$BUNDLED_ARCHIVE_DIR"

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

  val userModel2: SessionToken=>Route = (t : SessionToken) => userPrefix {userId => {pathPrefix("modelupload" / Segment.?) { modelNameOrId =>
  {pathEnd {
    post {
      entity(as[String]) { contents => {
        val request = new UploadArchiveRequest(database, userId, contents, modelNameOrId)
        completeRequest(request, t)
      }}}}}}}}

  val createTemplate: SessionToken=>Route = (t : SessionToken) => pathPrefix("models" / "users" / Segment / "templates" / Segment / "create" / Segment) {(userId, template, switchingKind) => { pathEnd { post {
    entity(as[String]) { x => {
      val obj = x.parseJson.asJsObject
      val code = obj.fields("code").convertTo[String]
      val vertices = obj.fields("vertices").asInstanceOf[JsArray]
      val subGraphs = obj.fields("subGraphs").asInstanceOf[JsArray]
      val edges = obj.fields("edges").asInstanceOf[JsArray]
      val specKind = obj.fields("specKind").convertTo[List[String]]
      val request = template match {
        case "controlledstability" => new CreateControlledStabilityTemplateRequest(userId, code, switchingKind, specKind, vertices, subGraphs, edges)
      }
      completeRequest(request, t)
    }}
  }}}}

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
}
