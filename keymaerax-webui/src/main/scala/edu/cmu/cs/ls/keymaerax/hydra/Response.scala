/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * HyDRA API Responses
 *  @author Nathan Fulton
 *  @author Stefan Mitsch
 *  @author Ran Ji
 */
package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.core.{Expression, Formula}
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser._
import spray.json._
import akka.http.scaladsl.marshalling.ToResponseMarshallable
import akka.http.scaladsl.marshallers.xml.ScalaXmlSupport._

import java.io.{PrintWriter, StringWriter}
import Helpers._
import edu.cmu.cs.ls.keymaerax.{Configuration, Logging}
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.btactics.macros._
import DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.btactics.SwitchedSystems.{Controlled, Guarded, SwitchedSystem, Timed}
import edu.cmu.cs.ls.keymaerax.lemma.Lemma
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration

import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer
import scala.collection.immutable
import scala.collection.immutable.Seq
import scala.util.Try
import scala.util.matching.Regex.Match
import scala.xml.Elem


/**
 * Responses are like views -- they shouldn't do anything except produce appropriately
 * formatted JSON from their parameters.
 *
 * To create a new response:
 * <ol>
 *   <li>Create a new object extending Response (perhaps with constructor arguments)</li>
 *   <li>override the json value with the json to be generated.</li>
 *   <li>override the schema value with Some(File(...)) containing the schema.</li>
 * </ol>
 *
 * See BooleanResponse for the simplest example.
 */
sealed trait Response {
  /**
   * Should be the name of a single file within resources/js/schema.
   */
  val schema: Option[String] = None

  /** Returns the response data in JSON format (unsupported by HtmlResponse). */
  def getJson: JsValue

  /** Returns the printed marshallable response. */
  def print: ToResponseMarshallable = getJson.compactPrint
}

/** Responds with a dynamically generated (server-side) HTML page. */
case class HtmlResponse(html: Elem) extends Response {
  override def getJson: JsValue = throw new UnsupportedOperationException("HTML response is no JSON data")
  override def print: ToResponseMarshallable = html
}

case class BooleanResponse(flag : Boolean, errorText: Option[String] = None) extends Response {
  override val schema: Option[String] = Some("BooleanResponse.js")

  def getJson: JsObject = errorText match {
    case Some(s) =>
      JsObject(
        "success" -> (if(flag) JsTrue else JsFalse),
        "type" -> JsNull,
        "errorText" -> JsString(s)
      )
    case None =>
      JsObject(
        "success" -> (if(flag) JsTrue else JsFalse),
        "type" -> JsNull
      )
  }
}

class PlainResponse(data: (String, JsValue)*) extends Response {
  override def getJson: JsValue = JsObject(data:_*)
}

class ModelListResponse(models: List[ModelPOJO]) extends Response {
  val objects: List[JsObject] = models.map(modelpojo => JsObject(
    "id" -> JsString(modelpojo.modelId.toString),
    "name" -> JsString(modelpojo.name),
    "date" -> JsString(modelpojo.date),
    "description" -> JsString(modelpojo.description),
    "pubLink" -> JsString(modelpojo.pubLink),
    "keyFile" -> JsString(modelpojo.keyFile),
    "title" -> JsString(modelpojo.title),
    "hasTactic" -> JsBoolean(modelpojo.tactic.isDefined),
    "numAllProofSteps" -> JsNumber(modelpojo.numAllProofSteps),
    "isExercise" -> JsBoolean(ArchiveParser.isExercise(modelpojo.keyFile)),
    "folder" -> (if (modelpojo.name.contains("/")) JsString(modelpojo.name.substring(0, modelpojo.name.indexOf('/'))) else JsNull)
  ))

  def getJson: JsValue = JsArray(objects:_*)
}

case class ModelUploadResponse(modelId: Option[String], errorText: Option[String]) extends Response {
  def getJson: JsValue = JsObject(
    "success" -> JsBoolean(modelId.isDefined),
    "errorText" -> JsString(errorText.getOrElse("")),
    "modelId" -> JsString(modelId.getOrElse("")))
}

case class ModelUpdateResponse(modelId: String, name: String, content: String, title: Option[String], description: Option[String], errorText: Option[String]) extends Response {
  def getJson: JsValue = JsObject(
    "success" -> JsBoolean(errorText.isEmpty),
    "errorText" -> JsString(errorText.getOrElse("")),
    "modelId" -> JsString(modelId),
    "name" -> JsString(name),
    "content" -> JsString(content),
    "title" -> JsString(title.getOrElse("")),
    "description" -> JsString(description.getOrElse(""))
  )
}

class UpdateProofNameResponse(proofId: String, newName: String) extends Response {
  def getJson: JsValue = JsArray()
}

/**
 *
 * @param proofs The list of proofs with their status in KeYmaera (proof, loadStatus).
 */
class ProofListResponse(proofs: List[(ProofPOJO, String)]) extends Response {
  override val schema: Option[String] = Some("prooflist.js")

  val objects : List[JsObject] = proofs.map({case (proof, loadStatus) => JsObject(
    "id" -> JsString(proof.proofId.toString),
    "name" -> JsString(proof.name),
    "description" -> JsString(proof.description),
    "date" -> JsString(proof.date),
    "modelId" -> JsString(proof.modelId.toString),
    "stepCount" -> JsNumber(proof.stepCount),
    "status" -> JsBoolean(proof.closed),
    "loadStatus" -> JsString(loadStatus)
  )})

  def getJson: JsValue = JsArray(objects:_*)
}

class UserLemmasResponse(proofs: List[(ProofPOJO, Option[(String, Lemma)])]) extends Response {
  lazy val objects : List[JsObject] = proofs.map({case (proof, lemma) => JsObject(
    "id" -> JsString(proof.proofId.toString),
    "name" -> (lemma match { case Some((n, _)) => JsString(n) case None => JsNull }),
    "conclusion" -> (lemma match {
      case Some((_, l)) => JsString(l.fact.conclusion.prettyString)
      case None => JsNull
    })
  )})

  override def getJson: JsValue = JsArray(objects:_*)
}

class GetModelResponse(model: ModelPOJO) extends Response {

  private def illustrationLinks(): List[String] = try {
    ArchiveParser.parser(model.keyFile).flatMap(_.info.get("Illustration"))
  } catch {
    case _: ParseException => Nil
  }

  def getJson: JsValue = JsObject(
    "id" -> JsString(model.modelId.toString),
    "name" -> JsString(model.name),
    "date" -> JsString(model.date),
    "description" -> JsString(model.description),
    "illustrations" -> JsArray(illustrationLinks().map(JsString(_)).toVector),
    "pubLink" -> JsString(model.pubLink),
    "keyFile" -> JsString(model.keyFile),
    "title" -> JsString(model.title),
    "hasTactic" -> JsBoolean(model.tactic.isDefined),
    "tactic" -> JsString(model.tactic.getOrElse("")),
    "numAllProofSteps" -> JsNumber(model.numAllProofSteps),
    "isExercise" -> JsBoolean(ArchiveParser.isExercise(model.keyFile))
  )
}

class GetModelTacticResponse(model: ModelPOJO) extends Response {
  def getJson: JsValue = JsObject(
    "modelId" -> JsString(model.modelId.toString),
    "modelName" -> JsString(model.name),
    "tacticBody" -> JsString(model.tactic.getOrElse(""))
  )
}

class ModelPlexMandatoryVarsResponse(model: ModelPOJO, vars: Set[Variable]) extends Response {
  def getJson: JsValue = JsObject(
    "modelid" -> JsString(model.modelId.toString),
    "mandatoryVars" -> JsArray(vars.map(v => JsString(v.prettyString)).toVector)
  )
}

abstract class ModelPlexResponse(model: ModelPOJO, code: String) extends Response {
  protected def prettierPrint(e: Expression): String = PrettierPrintFormatProvider(e, 80).print(e.prettyString)

  def getJson: JsValue = {
    JsObject(
      "modelid" -> JsString(model.modelId.toString),
      "modelname" -> JsString(model.name),
      "code" -> JsString(code),
      "source" -> JsString(prettierPrint(ArchiveParser(model.keyFile).head.expandedModel))
    )
  }
}

class ModelPlexArtifactResponse(model: ModelPOJO, artifact: Expression)
  extends ModelPlexResponse(model, PrettierPrintFormatProvider(artifact, 80).print(artifact.prettyString)) {
}

class ModelPlexMonitorResponse(model: ModelPOJO, artifact: Expression, proofArchive: String)
    extends ModelPlexArtifactResponse(model, artifact) {
  override def getJson: JsValue = {
    val artifact = super.getJson.asJsObject
    artifact.copy(artifact.fields + ("proof" -> JsString(proofArchive)))
  }
}

class ModelPlexSandboxResponse(model: ModelPOJO, conjecture: Formula, artifact: Expression)
    extends ModelPlexArtifactResponse(model, artifact) {
  override def getJson: JsValue = {
    val artifact = super.getJson.asJsObject
    artifact.copy(artifact.fields + ("conjecture" -> JsString(prettierPrint(conjecture))))
  }
}

class TestSynthesisResponse(model: ModelPOJO, metric: Formula,
                           //@todo class: List[(SeriesName, List[(Var->Val, SafetyMargin, Variance)])]
                            testCases: List[(String, List[(Map[Term, Term], Option[Number], Number)])]) extends Response {
  private val fmlHtml = JsString(UIKeYmaeraXPrettyPrinter("", plainText=false)(metric))
  private val fmlString = JsString(UIKeYmaeraXPrettyPrinter("", plainText=true)(metric))
  private val fmlPlainString = JsString(KeYmaeraXPrettyPrinter(metric))

  private val minRadius = 5  // minimum radius of bubbles even when all pre are equal to their post
  private val maxRadius = 30 // maximum radius of bubbles even when wildly different values

  private val Number(maxVariance) = testCases.flatMap(_._2).maxBy(_._3.value)._3

  private def radius(n: BigDecimal): BigDecimal =
    if (maxVariance > 0) minRadius + (maxRadius-minRadius)*(n/maxVariance)
    else minRadius

  private def scatterData(tc: List[(Map[Term, Term], Option[Number], Number)]) = JsArray(tc.zipWithIndex.map(
      { case ((_, safetyMargin, Number(variance)), idx) => JsObject(
    "x" -> JsNumber(idx),
    "y" -> (safetyMargin match { case Some(Number(sm)) => JsNumber(sm) case None => JsNumber(-1) }),
    "r" -> JsNumber(radius(variance))
  ) }):_*)

  // pre/post/labels/series
  private def prePostVals(vals: Map[Term, Term]): (JsArray, JsArray, JsArray, JsArray) = {
    val (pre, post) = vals.partition({ case (v, _) => v.isInstanceOf[BaseVariable] })
    val preByPost: Map[Term, Term] = post.map({
      case (post@FuncOf(Function(name, idx, Unit, Real, _), _), _) if name.endsWith("post") =>
        post -> Variable(name.substring(0, name.length-"post".length), idx)
      case (v, _) => v -> v
    })
    val preJson = pre.map({ case (v, Number(value)) => JsObject("v" -> JsString(v.prettyString), "val" -> JsNumber(value)) })
    val postJson = post.map({ case (v, Number(value)) => JsObject("v" -> JsString(preByPost(v).prettyString), "val" -> JsNumber(value)) })
    val sortedKeys = pre.keys.toList.sortBy(_.prettyString)
    val labels = sortedKeys.map(v => JsString(v.prettyString))
    val preSeries = sortedKeys.map(k => pre.get(k) match { case Some(Number(v)) => JsNumber(v) })
    val postSeries = sortedKeys.map({ case k@BaseVariable(n, i, _) =>
      post.get(FuncOf(Function(n + "post", i, Unit, Real), Nothing)) match {
        case Some(Number(v)) => JsNumber(v)
        case None => pre.get(k) match { case Some(Number(v)) => JsNumber(v) } //@note constants
      }
    })
    (JsArray(preJson.toVector), JsArray(postJson.toVector), JsArray(labels.toVector),
      JsArray(JsArray(preSeries.toVector), JsArray(postSeries.toVector)))
  }

  private def seriesData(data: List[(Map[Term, Term], Option[Number], Number)]): JsArray = JsArray(data.zipWithIndex.map({
    case ((vals: Map[Term, Term], safetyMargin, Number(variance)), idx) =>
      val (preVals, postVals, labels, series) = prePostVals(vals)
      JsObject(
        "name" -> JsString(""+idx),
        "safetyMargin" -> (safetyMargin match { case Some(Number(sm)) => JsNumber(sm) case None => JsNumber(-1) }),
        "variance" -> JsNumber(variance),
        "pre" -> preVals,
        "post" -> postVals,
        "labels" -> labels,
        "seriesData" -> series
      )
  }):_*)

  def getJson: JsValue = JsObject(
    "modelid" -> JsString(model.modelId.toString),
    "metric" -> JsObject(
      "html" -> fmlHtml,
      "string" -> fmlString,
      "plainString" -> fmlPlainString
    ),
    "plot" -> JsObject(
      "data" -> JsArray(testCases.map({ case (_, tc) => scatterData(tc) }):_*),
      "series" -> JsArray(testCases.map({ case (name, _) => JsString(name) }):_*),
      "labels" -> JsArray(JsString("Case"), JsString("Safety Margin"), JsString("Variance"))
    ),
    "caseInfos" -> JsArray(testCases.map({ case (name, data) => JsObject("series" -> JsString(name), "data" -> seriesData(data)) }):_*)
  )
}

class ModelPlexCCodeResponse(model: ModelPOJO, code: String) extends ModelPlexResponse(model, code) {

}

class LoginResponse(flag: Boolean, user: UserPOJO, sessionToken: Option[String]) extends Response {
  def getJson: JsValue = JsObject(
    "success" -> (if (flag) JsTrue else JsFalse),
    "sessionToken" -> (if (flag && sessionToken.isDefined) JsString(sessionToken.get) else JsFalse),
    "key" -> JsString("userId"),
    "value" -> JsString(user.userName.replaceAllLiterally("/", "%2F").replaceAllLiterally(":", "%3A")),
    "userAuthLevel" -> JsNumber(user.level),
    "askUseDefaultUser" -> (if (Configuration.getString(Configuration.Keys.USE_DEFAULT_USER).contains("false")) JsFalse else JsTrue),
    "type" -> JsString("LoginResponse")
  )
}

case class CreatedIdResponse(id: String) extends Response {
  def getJson: JsValue = JsObject("id" -> JsString(id))
}

class PossibleAttackResponse(val msg: String) extends Response with Logging {
  logger.error(s"POSSIBLE ATTACK: $msg")
  override def getJson: JsValue = new ErrorResponse(msg).getJson
}

class ErrorResponse(val msg: String, val exn: Throwable = null, val severity: String = "error") extends Response {
  private lazy val writer = new StringWriter
  private lazy val stacktrace =
    if (exn != null) {
      exn.printStackTrace(new PrintWriter(writer))
      writer.toString
        .replaceAll("[\\t]at spray\\.routing\\..*", "")
        .replaceAll("[\\t]at java\\.util\\.concurrent\\..*", "")
        .replaceAll("[\\t]at java\\.lang\\.Thread\\.run.*", "")
        .replaceAll("[\\t]at scala\\.Predef\\$\\.require.*", "")
        .replaceAll("[\\t]at akka\\.spray\\.UnregisteredActorRefBase.*", "")
        .replaceAll("[\\t]at akka\\.dispatch\\..*", "")
        .replaceAll("[\\t]at scala\\.concurrent\\.forkjoin\\..*", "")
        .replaceAll("[\\t]at scala\\.runtime\\.AbstractPartialFunction.*", "")
        .replaceAll("\\s+$|\\s*(\n)\\s*|(\\s)\\s*", "$1$2") //@note collapse newlines
    } else ""
  def getJson: JsValue = JsObject(
    "textStatus" -> (if (msg != null) JsString(msg.replaceAllLiterally("[Bellerophon Runtime]", "")) else JsString("")),
    "causeMsg" -> (if (exn != null && exn.getMessage != null) JsString(exn.getMessage.replaceAllLiterally("[Bellerophon Runtime", "")) else JsString("")),
    "errorThrown" -> JsString(stacktrace),
    "type" -> JsString(severity)
  )
}

class KvpResponse(val key: String, val value: String) extends Response {
  override def getJson: JsValue = JsObject(key -> JsString(value))
}

case class ParseErrorResponse(override val msg: String, expect: String, found: String, detailedMsg: String,
                         loc: Location, override val exn: Throwable = null) extends ErrorResponse(msg, exn) {
  override def getJson: JsValue = JsObject(super.getJson.asJsObject.fields ++ Map(
    "details" -> JsObject(
      "expect" -> JsString(expect),
      "found" -> JsString(found),
      "detailedMsg" -> JsString(detailedMsg)
    ),
    "location" -> JsObject(
      "line" -> JsNumber(loc.line),
      "column" -> JsNumber(loc.column)
    )
  ))
}

case class DefaultLoginResponse(triggerRegistration: Boolean) extends Response {
  override def getJson: JsObject = JsObject(Map(
    "type" -> JsString("LoginResponse"),
    "triggerRegistration" -> JsBoolean(triggerRegistration)))
}

class TacticErrorResponse(msg: String, tacticMsg: String, exn: Throwable = null)
    extends ErrorResponse(msg, exn) {
  override def getJson: JsValue = exn match {
    case _: BelleUnexpectedProofStateError =>
      JsObject(super.getJson.asJsObject.fields ++ Map(
        "tacticMsg" -> JsString(tacticMsg)
      ))
    case ex: CompoundCriticalException =>
      val exceptions = flatten(ex)
      val messages = exceptions.size + " tactic attempts failed:\n" + exceptions.zipWithIndex.map({
        case (x: BelleUnexpectedProofStateError, i) =>
          (i+1) + ". " + x.getMessage +
            ":\n" + x.proofState.subgoals.map(_.toString).mkString(",")
        case (x, i) => (i+1) + ". " + x.getMessage
      }).mkString("\n") + "\n"
      JsObject(super.getJson.asJsObject.fields.filter(_._1 != "textStatus") ++ Map(
        "textStatus" -> JsString(messages),
        "tacticMsg" -> JsString(tacticMsg)
      ))
    case _ =>
      JsObject(super.getJson.asJsObject.fields ++ Map(
        "tacticMsg" -> JsString(tacticMsg)
      ))
  }

  private def flatten(ex: BelleThrowable): List[BelleThrowable] = ex match {
    case ex: CompoundCriticalException => flatten(ex.left) ++ flatten(ex.right)
    case _ => ex :: Nil
  }
}

class ToolConfigErrorResponse(tool: String, msg: String) extends ErrorResponse(msg, null) {
  override def getJson: JsObject = JsObject(super.getJson.asJsObject.fields ++ Map("tool" -> JsString(tool)))
}

class GenericOKResponse() extends Response {
  def getJson: JsValue = JsObject(
    "success" -> JsTrue
  )
}

class UnimplementedResponse(callUrl: String) extends ErrorResponse("Call unimplemented: " + callUrl) {}

class ProofStatusResponse(proofId: String, status: String, error: Option[String] = None) extends Response {
  override val schema: Option[String] = Some("proofstatus.js")
  def getJson: JsValue = JsObject(
    "proofId" -> JsString(proofId),
    "type" -> JsString("ProofLoadStatus"),
    "status" -> JsString(status),
    "textStatus" -> JsString(status + ": " + proofId),
    "errorThrown" -> JsString(error.getOrElse(""))
  )
}
class ProofIsLoadingResponse(proofId: String) extends ProofStatusResponse(proofId, "loading")
class ProofNotLoadedResponse(proofId: String) extends ProofStatusResponse(proofId, "notloaded")
class ProofIsLoadedResponse(proofId: String) extends ProofStatusResponse(proofId, "loaded")
// progress "open": open goals
// progress "closed": no open goals but not checked for isProved
class ProofProgressResponse(proofId: String, isClosed: Boolean)
  extends ProofStatusResponse(proofId, if (isClosed) "closed" else "open")

class ProofVerificationResponse(proofId: String, provable: ProvableSig, tactic: String) extends Response {
  override def getJson: JsValue = JsObject(
    "proofId" -> JsString(proofId),
    "isProved" -> JsBoolean(provable.isProved),
    "provable" -> JsString(provable.underlyingProvable.toString),
    "tactic" -> JsString(tactic))
}

class GetProblemResponse(proofid: String, tree: String) extends Response {
  def getJson: JsValue = JsObject(
    "proofid" -> JsString(proofid),
    "proofTree" -> JsonParser(tree)
  )
}

case class RunBelleTermResponse(proofId: String, nodeId: String, taskId: String, info: String) extends Response {
  def getJson: JsValue = JsObject(
    "proofId" -> JsString(proofId),
    "nodeId" -> JsString(nodeId),
    "taskId" -> JsString(taskId),
    "type" -> JsString("runbelleterm"),
    "info" -> JsString(info)
  )
}

case class TaskStatusResponse(proofId: String, nodeId: String, taskId: String, status: String,
                              progress: Option[(Option[(BelleExpr, Long)], Seq[(BelleExpr, Either[BelleValue, BelleThrowable])])]) extends Response {
  def getJson: JsValue = {
    JsObject(
      "proofId" -> JsString(proofId),
      "parentId" -> JsString(nodeId),
      "taskId" -> JsString(taskId),
      "status" -> JsString(status),
      "type" -> JsString("taskstatus"),
      "currentStep" -> progress.map(p => JsObject(
        "ruleName" -> p._1.map(c => JsString(c._1.prettyString)).getOrElse(JsNull),
        "duration" -> p._1.map(c => JsNumber(c._2)).getOrElse(JsNull),
        "stepStatus" -> JsNull
      )).getOrElse(JsNull),
      "progress" -> progress.map(p => JsArray(
        p._2.map(e => JsString(e._1.prettyString)):_*
      )).getOrElse(JsArray())
    )
  }

}

case class TaskResultResponse(proofId: String, parent: ProofTreeNode, marginLeft: Int, marginRight: Int, progress: Boolean = true) extends Response {
  private lazy val openChildren = parent.children.filter(_.numSubgoals > 0)

  def getJson: JsValue = JsObject(
    "proofId" -> JsString(proofId),
    "parent" -> JsObject(
      "id" -> JsString(parent.id.toString),
      "children" -> JsArray(openChildren.map(c => JsString(c.id.toString)):_*)
    ),
    "newNodes" -> JsArray(nodesJson(openChildren, marginLeft, marginRight).map(_._2):_*),
    "progress" -> JsBoolean(progress),
    "type" -> JsString("taskresult")
  )
}

case class NodeChildrenResponse(proofId: String, parent: ProofTreeNode, marginLeft: Int, marginRight: Int) extends Response {
  def getJson: JsValue = JsObject(
    "proofId" -> JsString(proofId),
    "parent" -> JsObject(
      "id" -> JsString(parent.id.toString),
      "children" -> JsArray(parent.children.map(c => JsString(c.id.toString)):_*)
    ),
    "newNodes" -> JsArray(nodesJson(parent.children, marginLeft, marginRight).map(_._2):_*),
    "progress" -> JsBoolean(true)
  )
}

case class ProofNodeSequentResponse(proofId: String, node: ProofTreeNode, marginLeft: Int, marginRight: Int) extends Response {
  def getJson: JsValue = JsObject(
    "proofId" -> JsString(proofId),
    "nodeId" -> JsString(node.id.toString),
    "sequent" -> (node.goal match { case None => JsNull case Some(goal) => sequentJson(goal, marginLeft, marginRight) })
  )
}

class UpdateResponse(update: String) extends Response {
  def getJson: JsValue = JsObject(
    "type" -> JsString("update"),
    "events" -> JsonParser(update)
  )
}

class ProofTreeResponse(tree: String) extends Response {
  def getJson: JsValue = JsObject(
    "type" -> JsString("proof"),
    "tree" -> JsonParser(tree)
  )
}

case class ProofLemmasResponse(lemmas: List[(String, Int)]) extends Response {
  def getJson: JsValue = JsObject({
    "lemmas" -> JsArray(lemmas.map(l => JsObject(
      "name" -> JsString(l._1),
      "proofId" -> JsNumber(l._2)
    )):_*)
  })
}

case class OpenProofResponse(proof: ProofPOJO, loadStatus: String) extends Response {
  override val schema: Option[String] = Some("proof.js")
  def getJson: JsValue = JsObject(
    "id" -> JsString(proof.proofId.toString),
    "name" -> JsString(proof.name),
    "description" -> JsString(proof.description),
    "date" -> JsString(proof.date),
    "modelId" -> JsString(proof.modelId.toString),
    "stepCount" -> JsNumber(proof.stepCount),
    "status" -> JsBoolean(proof.closed),
    "tactic" -> (proof.tactic match { case None => JsNull case Some(t) => JsString(t) }),
    "loadStatus" -> JsString(loadStatus)
  )
}

class ProofAgendaResponse(tasks: List[(ProofPOJO, List[Int], String)]) extends Response {
  override val schema: Option[String] = Some("proofagenda.js")
  val objects: List[JsObject] = tasks.map({ case (proofPojo, nodeId, nodeJson) => JsObject(
    "proofId" -> JsString(proofPojo.proofId.toString),
    "nodeId" -> Helpers.nodeIdJson(nodeId),
    "proofNode" -> JsonParser(nodeJson)
  )})

  def getJson: JsValue = JsArray(objects:_*)
}

/** JSON conversions for frequently-used response formats */
object Helpers {

  /** Stateful format provider to read off whitespace and line breaks from a pretty-printed string. */
  case class HtmlPrettyPrintFormatProvider(format: String, wsPrinter: String => String =
      _.replaceAllLiterally("\n", "<br/>").replaceAll("\\s", "&nbsp;"))
    extends PrettyPrintFormatProvider(format, wsPrinter) {

  }

  /** Noop format provider. */
  class NoneFormatProvider extends FormatProvider {
    override def printWS(check: String): String = ""
    override def print(next: String): String = next
  }

  def sequentJson(sequent: Sequent, marginLeft: Int, marginRight: Int): JsValue = {
    def fmlsJson(isAnte: Boolean, fmls: IndexedSeq[Formula]): JsValue = {
      JsArray(fmls.zipWithIndex.map { case (fml, i) =>
        /* Formula ID is formula number followed by comma-separated PosInExpr.
         formula number = strictly positive if succedent, strictly negative if antecedent, 0 is never used
        */
        val idx = if (isAnte) (-i)-1 else i+1
        val fmlString = JsString(UIKeYmaeraXPrettyPrinter(idx.toString, plainText=true)(fml))

        val format = new KeYmaeraXPrettierPrinter(if (isAnte) marginLeft else marginRight)(fml)
        val fmlJson = printJson(PosInExpr(), fml, HtmlPrettyPrintFormatProvider(format))(Position(idx), fml)
        JsObject(
          "id" -> JsString(idx.toString),
          "formula" -> JsObject(
            "json" -> fmlJson,
            "string" -> fmlString
          )
        )
      }.toVector)
    }
    JsObject(
      "ante" -> fmlsJson(isAnte = true, sequent.ante),
      "succ" -> fmlsJson(isAnte = false, sequent.succ)
    )
  }

  private def printObject(text: String, kind: String = "text"): JsValue = JsObject("text"->JsString(text), "kind" -> JsString(kind))
  private def print(text: String, fp: FormatProvider, kind: String = "text"): JsValue = printObject(fp.print(text), kind)
  private def print(q: PosInExpr, text: String, kind: String, fp: FormatProvider)(implicit top: Position): JsValue =
    JsObject("id" -> JsString(top + (if (q.pos.nonEmpty) "," + q.pos.mkString(",") else "")),
      "text"->JsString(fp.print(text)), "kind" -> JsString(kind))
  private def print(q: PosInExpr, kind: String, hasStep: Boolean, isEditable: Boolean, plainText: => String,
                    children: Seq[JsValue])(implicit top: Position): JsValue = {
    JsObject(
      "id" -> JsString(top + (if (q.pos.nonEmpty) "," + q.pos.mkString(",") else "")),
      "kind" -> JsString(kind),
      "plain" -> (if (isEditable || q.pos.isEmpty) JsString(plainText) else JsNull),
      "step" -> JsString(if (hasStep) "has-step" else "no-step"),
      "editable" -> JsString(if (isEditable) "editable" else "not-editable"),
      "children"->JsArray(children:_*))
  }

  private def op(expr: Expression, fp: FormatProvider, opLevel: String = "op"): JsValue = expr match {
    // terms
    case _: Minus        => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&minus;", opLevel + " k4-term-op")
    case _: Neg          => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&minus;", opLevel + " k4-term-op")
    case _: Term         => printObject(fp.print(OpSpec.op(expr).opcode), opLevel + " k4-term-op")
    // formulas
    case _: NotEqual     => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&ne;", opLevel + " k4-cmpfml-op")
    case _: GreaterEqual => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&ge;", opLevel + " k4-cmpfml-op")
    case _: Greater      => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&gt;", opLevel + " k4-cmpfml-op")
    case _: LessEqual    => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&le;", opLevel + " k4-cmpfml-op")
    case _: Less         => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&lt;", opLevel + " k4-cmpfml-op")
    case _: Forall       => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&forall;", opLevel + " k4-fml-op")
    case _: Exists       => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&exist;", opLevel + " k4-fml-op")
    case _: Not          => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&not;", opLevel + " k4-propfml-op")
    case _: And          => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&and;", opLevel + " k4-propfml-op")
    case _: Or           => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&or;", opLevel + " k4-propfml-op")
    case _: Imply        => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&rarr;", opLevel + " k4-propfml-op")
    case _: Equiv        => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&#8596;", opLevel + " k4-propfml-op")
    case _: Formula      => printObject(fp.printWS(OpSpec.op(expr).opcode) + OpSpec.op(expr).opcode, opLevel + " k4-fml-op")
    // programs
    case _: Choice       => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&cup;", opLevel + " k4-prg-op")
    case _: Program      => printObject(fp.printWS(OpSpec.op(expr).opcode) + OpSpec.op(expr).opcode, opLevel + " k4-prg-op")
    case _ => printObject(fp.printWS(OpSpec.op(expr).opcode) + OpSpec.op(expr).opcode, opLevel)
  }

  private def skipParens(expr: Modal): Boolean = OpSpec.op(expr.child) <= OpSpec.op(expr)
  private def skipParens(expr: Quantified): Boolean = OpSpec.op(expr.child) <= OpSpec.op(expr)
  private def skipParens(expr: UnaryComposite): Boolean =
    if (expr.isInstanceOf[Term]) OpSpec.op(expr.child) <= OpSpec.op(expr) && !leftMostLeaf(expr.child).exists(_.isInstanceOf[Number])
    else OpSpec.op(expr.child) <= OpSpec.op(expr)
  private def skipParensLeft(expr: BinaryComposite): Boolean =
    OpSpec.op(expr.left) < OpSpec.op(expr) || OpSpec.op(expr.left) <= OpSpec.op(expr) &&
      OpSpec.op(expr).assoc == LeftAssociative && OpSpec.op(expr.left).assoc == LeftAssociative
  private def skipParensRight(expr: BinaryComposite): Boolean =
    OpSpec.op(expr.right) < OpSpec.op(expr) || OpSpec.op(expr.right) <= OpSpec.op(expr) &&
      OpSpec.op(expr).assoc == RightAssociative && OpSpec.op(expr.right).assoc == RightAssociative

  private def wrapLeft(expr: BinaryComposite, left: => JsValue, fp: FormatProvider): List[JsValue] =
    if (skipParensLeft(expr)) left::Nil else print("(", fp)::left::print(")", fp)::Nil
  private def wrapRight(expr: BinaryComposite, right: => JsValue, fp: FormatProvider): List[JsValue] =
    if (skipParensRight(expr)) right::Nil else print("(", fp)::right::print(")", fp)::Nil
  private def wrapChild(expr: UnaryComposite, child: => JsValue, fp: FormatProvider): List[JsValue] =
    if (skipParens(expr)) child::Nil else print("(", fp)::child::print(")", fp)::Nil
  private def wrapChild(expr: Quantified, child: => JsValue, fp: FormatProvider): List[JsValue] =
    if (skipParens(expr)) child::Nil else print("(", fp)::child::print(")", fp)::Nil
  private def wrapChild(expr: Modal, child: => JsValue, fp: FormatProvider): List[JsValue] =
    if (skipParens(expr)) child::Nil else print("(", fp)::child::print(")", fp)::Nil
  private def pwrapLeft(expr: BinaryCompositeProgram, left: => List[JsValue], fp: FormatProvider): List[JsValue] =
    if (skipParensLeft(expr)) left else print("{", fp, "prg-open")+:left:+print("}", fp, "prg-close")
  private def pwrapRight(expr: BinaryCompositeProgram, right: => List[JsValue], fp: FormatProvider): List[JsValue] =
    if (skipParensRight(expr)) right else print("{", fp, "prg-open")+:right:+print("}", fp, "prg-close")

  @tailrec
  private def leftMostLeaf(t: Expression): Option[Expression] = t match {
    case _: UnaryComposite => None
    case b: BinaryComposite => leftMostLeaf(b.left)
    case x => Some(x)
  }

  private def printJson(q: PosInExpr, expr: Expression, fp: FormatProvider)(implicit top: Position, topExpr: Expression): JsValue = {
    val hasStep = UIIndex.allStepsAt(expr, Some(top++q), None, Nil).nonEmpty
    val parent = if (q.pos.isEmpty) None else topExpr match {
      case t: Term => t.sub(q.parent)
      case f: Formula => f.sub(q.parent)
      case p: Program => p.sub(q.parent)
      case _ => None
    }
    val isEditable = (expr, parent) match {
      // edit "top-most" formula only
      case (f: Formula, Some(_: Program | _: Modal) | None) => f.isFOL
      case (_, _) => false
    }

    expr match {
      case f: ComparisonFormula =>
        print(q, "formula", hasStep, isEditable, expr.prettyString, wrapLeft(f, printJson(q ++ 0, f.left, fp), fp) ++ (op(f, fp)::Nil) ++ wrapRight(f, printJson(q ++ 1, f.right, fp), fp))
      case DifferentialFormula(g) => print(q, "formula", hasStep, isEditable, expr.prettyString,
        print("(", fp) :: print(g.prettyString, fp) :: print(")", fp) :: op(expr, fp) :: Nil)
      case f: Quantified => print(q, "formula", hasStep, isEditable, expr.prettyString,
        op(f, fp) :: print(f.vars.map(_.prettyString).mkString(","), fp) :: Nil ++ wrapChild(f, printJson(q ++ 0, f.child, fp), fp))
      case f: Box => print(q, "formula", hasStep, isEditable, expr.prettyString,
        print("[", fp, "mod-open")::printJson(q ++ 0, f.program, fp) :: print("]", fp, "mod-close") :: Nil ++ wrapChild(f, printJson(q ++ 1, f.child, fp), fp))
      case f: Diamond => print(q, "formula", hasStep, isEditable, expr.prettyString,
        print("<", fp, "mod-open") :: printJson(q ++ 0, f.program, fp) :: print(">", fp, "mod-close") :: Nil ++ wrapChild(f, printJson(q ++ 1, f.child, fp), fp))
      case f: UnaryCompositeFormula => print(q, "formula", hasStep, isEditable, expr.prettyString,
        op(f, fp) +: wrapChild(f, printJson(q ++ 0, f.child, fp), fp))
      case _: AtomicFormula => print(q, "formula", hasStep, isEditable, expr.prettyString, print(expr.prettyString, fp) :: Nil)
      case f: BinaryCompositeFormula => print(q, "formula", hasStep, isEditable, expr.prettyString,
        wrapLeft(f, printJson(q ++ 0, f.left, fp), fp) ++ (op(f, fp)::Nil) ++ wrapRight(f, printJson(q ++ 1, f.right, fp), fp))
      case p: Program => print(q, "program", hasStep=false, isEditable=false, expr.prettyString, printPrgJson(q, p, fp))
      case d: Differential => print(q, expr.prettyString, "term", fp)
      case t@Neg(Number(_)) => print(q, "term", hasStep, isEditable, expr.prettyString, op(t, fp) +: (print("(", fp)::printJson(q ++ 0, t.child, fp)::print(")", fp)::Nil))
      case t: UnaryCompositeTerm => print(q, "term", hasStep, isEditable, expr.prettyString, op(t, fp) +: wrapChild(t, printJson(q ++ 0, t.child, fp), fp))
      case t: BinaryCompositeTerm => print(q, "term", hasStep, isEditable, expr.prettyString,
        wrapLeft(t, printJson(q ++ 0, t.left, fp), fp) ++ (op(t, fp)::Nil) ++ wrapRight(t, printJson(q ++ 1, t.right, fp), fp))
      case _ => print(q, expr.prettyString, "term", fp)
    }
  }

  private def printPrgJson(q: PosInExpr, expr: Program, fp: FormatProvider)(implicit top: Position, topExpr: Expression): List[JsValue] = expr match {
    case Assign(x, e) => printJson(q ++ 0, x, fp)::op(expr, fp, "topop")::printJson(q ++ 1, e, fp)::print(";", fp)::Nil
    case AssignAny(x) => printJson(q ++ 0, x, fp)::op(expr, fp, "topop")::print(";", fp)::Nil
    case Test(f) => op(expr, fp, "topop")::printJson(q ++ 0, f, fp)::print(";", fp)::Nil
    case t: UnaryCompositeProgram => print("{", fp, "prg-open")+:printRecPrgJson(q ++ 0, t.child, fp):+print("}", fp, "prg-close"):+op(t, fp, "topop")
    case t: Compose => pwrapLeft(t, printRecPrgJson(q ++ 0, t.left, fp), fp)++(print(q, "", "topop k4-prg-op", fp)::Nil)++pwrapRight(t, printRecPrgJson(q ++ 1, t.right, fp), fp)
    case t: BinaryCompositeProgram => pwrapLeft(t, printRecPrgJson(q ++ 0, t.left, fp), fp) ++ (op(t, fp, "topop")::Nil) ++ pwrapRight(t, printRecPrgJson(q ++ 1, t.right, fp), fp)
    case ODESystem(ode, f) if f != True => print("{", fp, "prg-open")::printJson(q ++ 0, ode, fp)::print(q, "&", "topop k4-prg-op", fp)::printJson(q ++ 1, f, fp)::print("}", fp, "prg-close")::Nil
    case ODESystem(ode, f) if f == True => print("{", fp, "prg-open")::printJson(q ++ 0, ode, fp)::print("}", fp, "prg-close")::Nil
    case AtomicODE(xp, e) => printJson(q ++ 0, xp, fp)::op(expr, fp, "topop")::printJson(q ++ 1, e, fp)::Nil
    case t: DifferentialProduct => printJson(q ++ 0, t.left, fp)::op(t, fp, "topop")::printJson(q ++ 1, t.right, fp)::Nil
    case c: DifferentialProgramConst => print(c.prettyString, fp)::Nil
    case c: ProgramConst => print(c.asString /* needs to be consistent with OpSpec.statementSemicolon (inaccessible here) */ + ";", fp)::Nil
    case c: SystemConst => print(c.asString /* needs to be consistent with OpSpec.statementSemicolon (inaccessible here) */ + ";", fp)::Nil
  }

  private def printRecPrgJson(q: PosInExpr, expr: Program, fp: FormatProvider)(implicit top: Position, topExpr: Expression): List[JsValue] = expr match {
    case Assign(x, e) => printJson(q ++ 0, x, fp)::op(expr, fp)::printJson(q ++ 1, e, fp)::print(";", fp)::Nil
    case AssignAny(x) => printJson(q ++ 0, x, fp)::op(expr, fp)::print(";", fp)::Nil
    case Test(f) => op(expr, fp)::printJson(q ++ 0, f, fp)::print(";", fp)::Nil
    case t: UnaryCompositeProgram => print("{", fp, "prg-open")+:printRecPrgJson(q ++ 0, t.child, fp):+print("}", fp, "prg-close"):+op(t, fp)
    case t: Compose => pwrapLeft(t, printRecPrgJson(q ++ 0, t.left, fp), fp) ++ pwrapRight(t, printRecPrgJson(q ++ 1, t.right, fp), fp)
    case t: BinaryCompositeProgram => pwrapLeft(t, printRecPrgJson(q ++ 0, t.left, fp), fp) ++ (op(t, fp)::Nil) ++ pwrapRight(t, printRecPrgJson(q ++ 1, t.right, fp), fp)
    case ODESystem(ode, f) if f != True => print("{", fp, "prg-open")::printJson(q ++ 0, ode, fp)::print("&", fp)::printJson(q ++ 1, f, fp)::print("}", fp, "prg-close")::Nil
    case ODESystem(ode, f) if f == True => print("{", fp, "prg-open")::printJson(q ++ 0, ode, fp)::print("}", fp, "prg-close")::Nil
    case AtomicODE(xp, e) => printJson(q ++ 0, xp, fp)::op(expr, fp)::printJson(q ++ 1, e, fp)::Nil
    case t: DifferentialProduct => printJson(q ++ 0, t.left, fp)::op(t, fp)::printJson(q ++ 1, t.right, fp)::Nil
    case c: DifferentialProgramConst => print(c.prettyString, fp)::Nil
    case c: ProgramConst => print(c.asString /* needs to be consistent with OpSpec.statementSemicolon (inaccessible here) */ + ";", fp)::Nil
    case c: SystemConst => print(c.asString /* needs to be consistent with OpSpec.statementSemicolon (inaccessible here) */ + ";", fp)::Nil
  }

  /** Only first node's sequent is printed. */
  def nodesJson(nodes: List[ProofTreeNode], marginLeft: Int, marginRight: Int, printAllSequents: Boolean = false): List[(String, JsValue)] = {
    if (nodes.isEmpty) Nil
    else nodeJson(nodes.head, withSequent=true, marginLeft, marginRight) +: nodes.tail.map(nodeJson(_, withSequent=printAllSequents, marginLeft, marginRight))
  }

  def nodeJson(node: ProofTreeNode, withSequent: Boolean, marginLeft: Int, marginRight: Int): (String, JsValue) = {
    val id = JsString(node.id.toString)
    val sequent =
      if (withSequent) node.goal match { case None => JsNull case Some(goal) => sequentJson(goal, marginLeft, marginRight) }
      else JsNull
    val childrenIds = JsArray(node.children.map(s => JsString(s.id.toString)):_*)
    val parent = node.parent.map(n => JsString(n.id.toString)).getOrElse(JsNull)

    val posLocator =
      if (node.maker.isEmpty || node.maker.get.isEmpty) None
      else Try(BelleParser(node.maker.get)).toOption match { //@todo probably performance bottleneck
        case Some(pt: AppliedPositionTactic) => Some(pt.locator)
        case Some(pt: AppliedDependentPositionTactic) => Some(pt.locator)
        case _ => None
      }

    (node.id.toString, JsObject(
      "id" -> id,
      "isClosed" -> JsBoolean(node.numSubgoals <= 0),
      "sequent" -> sequent,
      "children" -> childrenIds,
      "rule" -> ruleJson(node.makerShortName.getOrElse(""), posLocator),
      "labels" -> JsArray(node.label.map(_.components).getOrElse(Nil).map(c => JsString(c.label)).toVector),
      "parent" -> parent))
  }

  def sectionJson(section: List[String]): JsValue = {
    JsObject("path" -> JsArray(section.map(JsString(_)):_*))
  }

  def deductionJson(deduction: List[List[String]]): JsValue =
    JsObject("sections" -> JsArray(deduction.map(sectionJson):_*))

  def itemJson(item: AgendaItem): (String, JsValue) = {
    val value = JsObject(
      "id" -> JsString(item.id),
      "name" -> JsString(item.name),
      "proofId" -> JsString(item.proofId),
      "deduction" -> deductionJson(List(item.path)))
    (item.id, value)
  }

  def nodeIdJson(n: List[Int]): JsValue = JsNull
  def proofIdJson(n: String): JsValue = JsString(n)

  def ruleJson(ruleName: String, pos: Option[PositionLocator]): JsValue = {
    val belleTerm = ruleName.split("\\(")(0)
    val (name, codeName, asciiName, longName, maker, derivation: JsValue) = Try(DerivationInfo.ofCodeName(belleTerm)).toOption match {
      case Some(di) => (di.display.name, di.codeName, di.display.asciiName, di.longDisplayName, ruleName,
          ApplicableAxiomsResponse(Nil, Map.empty, topLevel=true, pos).derivationJson(di).fields.getOrElse("derivation", JsNull))
      case None => (ruleName, ruleName, ruleName, ruleName, ruleName, JsNull)
    }

    JsObject(
      "id" -> JsString(name),
      "name" -> JsString(name),
      "codeName" -> JsString(codeName),
      "asciiName" -> JsString(asciiName),
      "longName" -> JsString(longName),
      "maker" -> JsString(maker), //@note should be equal to codeName
      "pos" -> (pos match {
        case Some(Fixed(p, _, _)) => JsString(p.prettyString)
        case _ => JsString("")
      }),
      "derivation" -> derivation
    )
  }

  def agendaItemJson(item: AgendaItemPOJO): JsValue = {
    JsObject(
      "agendaItemId" -> JsString(item.initialProofNode.toString),
      "proofId" -> JsString(item.proofId.toString),
      "displayName" -> JsString(item.displayName)
    )
  }
}

case class AgendaAwesomeResponse(modelId: String, proofId: String, root: ProofTreeNode, leaves: List[ProofTreeNode],
                                 agenda: List[AgendaItem], closed: Boolean, marginLeft: Int, marginRight: Int) extends Response {
  override val schema: Option[String] = Some("agendaawesome.js")

  private lazy val proofTree = {
    val theNodes: List[(String, JsValue)] = nodeJson(root, withSequent=false, marginLeft, marginRight) +: nodesJson(leaves, marginLeft, marginRight)
    JsObject(
      "id" -> proofIdJson(proofId),
      "nodes" -> JsObject(theNodes.toMap),
      "root" -> JsString(root.id.toString),
      "isProved" -> JsBoolean(root.isProved)
    )
  }

  private lazy val agendaItems = JsObject(agenda.map(itemJson):_*)

  def getJson: JsValue = JsObject (
    "modelId" -> JsString(modelId),
    "proofTree" -> proofTree,
    "agendaItems" -> agendaItems,
    "closed" -> JsBoolean(closed)
  )
}

class GetAgendaItemResponse(item: AgendaItemPOJO) extends Response {
  def getJson: JsValue = agendaItemJson(item)
}

class ProofTaskNodeResponse(node: ProofTreeNode, marginLeft: Int, marginRight: Int) extends Response {
  def getJson: JsValue = nodeJson(node, withSequent=true, marginLeft, marginRight)._2
}

class GetPathAllResponse(path: List[ProofTreeNode], parentsRemaining: Int, marginLeft: Int, marginRight: Int) extends Response {
  def getJson: JsValue =
    JsObject (
      "numParentsUntilComplete" -> JsNumber(parentsRemaining),
      "path" -> JsArray(path.map(nodeJson(_, withSequent=true, marginLeft, marginRight)._2):_*)
    )
}

class GetBranchRootResponse(node: ProofTreeNode, marginLeft: Int, marginRight: Int) extends Response {
  def getJson: JsValue = nodeJson(node, withSequent=true, marginLeft, marginRight)._2
}

case class LemmasResponse(infos: List[ProvableInfo]) extends Response {
  override def getJson: JsValue = {
    val json = infos.map(i =>
      JsObject(
        "name" -> JsString(i.canonicalName),
        "codeName" -> JsString(i.codeName),
        "defaultKeyPos" -> {
          val key = AxIndex.axiomIndex(i)._1
          JsString(key.pos.mkString("."))
        },
        "displayInfo" -> (i.display match {
          case AxiomDisplayInfo(_, f) => JsString(f)
          case _ => JsNull
        }),
        "displayInfoParts" -> RequestHelper.jsonDisplayInfoComponents(i)))

    JsObject("lemmas" -> JsArray(json:_*))
  }
}

case class ApplicableAxiomsResponse(derivationInfos: List[(DerivationInfo, Option[DerivationInfo])],
                                    suggestedInput: Map[ArgInfo, Expression], topLevel: Boolean,
                                    suggestedPosition: Option[PositionLocator] = None) extends Response {
  def inputJson(input: ArgInfo): JsValue = {
    (suggestedInput.get(input), input) match {
      case (Some(e), FormulaArg(name, _)) =>
        JsObject (
          "type" -> JsString(input.sort),
          "param" -> JsString(name),
          "value" -> JsString(e.prettyString)
        )
      case (_, ListArg(ai)) => //@todo suggested input for Formula*
        JsObject(
          "type" -> JsString(input.sort),
          "elementType" -> JsString(ai.sort),
          "param" -> JsString(ai.name)
        )
      case _ =>
        JsObject (
          "type" -> JsString(input.sort),
          "param" -> JsString(input.name)
        )
    }
  }

  def inputsJson(info: List[ArgInfo]): JsArray = {
    info match {
      case Nil => JsArray()
      case inputs => JsArray(inputs.map(inputJson):_*)
    }
  }

  private def helpJson(codeName: String): JsString = {
    val helpResource = getClass.getResourceAsStream(s"/help/axiomsrules/$codeName-help.html")
    if (helpResource == null) JsString("")
    else JsString(scala.io.Source.fromInputStream(helpResource)(scala.io.Codec.UTF8).mkString)
  }

  def axiomJson(info: DerivationInfo): JsObject = {
    val formulaText =
      (info, info.display) match {
        case (_, AxiomDisplayInfo(_, formulaDisplay)) => formulaDisplay
        case (_, InputAxiomDisplayInfo(_, formulaDisplay, _)) => formulaDisplay
        case (info: AxiomInfo, _) => info.formula.prettyString
      }
    JsObject(
      "type" -> JsString("axiom"),
      "formula" -> JsString(formulaText),
      "codeName" -> JsString(info.codeName),
      "canonicalName" -> JsString(info.canonicalName),
      "longName" -> JsString(info.longDisplayName),
      "defaultKeyPos" -> (info match {
        case pi: ProvableInfo =>
          val key = AxIndex.axiomIndex(pi)._1
          JsString(key.pos.mkString("."))
        case _ => JsString("0")
      }),
      "displayInfoParts" -> (info match {
        case pi: ProvableInfo => RequestHelper.jsonDisplayInfoComponents(pi)
        case _ => JsNull
      }),
      "input" -> inputsJson(info.inputs),
      "help" -> helpJson(info.codeName)
    )
  }

  def tacticJson(info: DerivationInfo): JsObject = {
    JsObject(
      "type" -> JsString("tactic"),
      "expansible" -> JsBoolean(info.revealInternalSteps),
      "input" -> inputsJson(info.inputs),
      "help" -> helpJson(info.codeName)
    )
  }

  def sequentJson(sequent:SequentDisplay): JsValue = {
    val json = JsObject (
    "ante" -> JsArray(sequent.ante.map(JsString(_)):_*),
    "succ" -> JsArray(sequent.succ.map(JsString(_)):_*),
    "isClosed" -> JsBoolean(sequent.isClosed)
    )
   json
  }

  def ruleJson(info: DerivationInfo, conclusion: SequentDisplay, premises: List[SequentDisplay]): JsObject = {
    val conclusionJson = sequentJson(conclusion)
    val premisesJson = JsArray(premises.map(sequentJson):_*)
    JsObject(
      "type" -> JsString("sequentrule"),
      "expansible" -> JsBoolean(info.revealInternalSteps),
      "conclusion" -> conclusionJson,
      "premise" -> premisesJson,
      "input" -> inputsJson(info.inputs),
      "help" -> helpJson(info.codeName)
    )
  }

  def derivationJson(derivationInfo: DerivationInfo): JsObject = {
    val derivation = derivationInfo match {
      case info: AxiomInfo => axiomJson(info)
      case info: DerivationInfo => (info, info.display) match {
        case (_, _: SimpleDisplayInfo) => tacticJson(info)
        case (pi: DerivationInfo, _: AxiomDisplayInfo) => axiomJson(pi)
        case (pi: DerivationInfo, _: InputAxiomDisplayInfo) => axiomJson(pi) //@todo usually those have tactics with RuleDisplayInfo
        case (_, RuleDisplayInfo(_, conclusion, premises)) => ruleJson(info, conclusion, premises)
        case (_, TacticDisplayInfo(_, conclusion, premises, ctxConc, ctxPrem)) =>
          if (topLevel) ruleJson(info, conclusion, premises)
          else ruleJson(info, ctxConc, ctxPrem)
        case (_, _: AxiomDisplayInfo | _: InputAxiomDisplayInfo) =>
          throw new IllegalArgumentException(s"Unexpected derivation info $derivationInfo displays as axiom but is not AxiomInfo")
      }
    }
    JsObject(
      "id" -> new JsString(derivationInfo.codeName),
      "name" -> new JsString(derivationInfo.display.name),
      "asciiName" -> new JsString(derivationInfo.display.asciiName),
      "codeName" -> new JsString(derivationInfo.codeName),
      "longName" -> new JsString(derivationInfo.longDisplayName),
      "displayLevel" -> new JsString(derivationInfo.displayLevel.name),
      "derivation" -> derivation
    )
  }

  private def posJson(pos: Option[PositionLocator]): JsValue = pos match {
    case Some(Fixed(p, _, _)) => new JsString(p.toString)
    case Some(Find(_, _, _: AntePosition, _, _)) => new JsString("L")
    case Some(Find(_, _, _: SuccPosition, _, _)) => new JsString("R")
    case _ => JsNull
  }

  def derivationJson(info: (DerivationInfo, Option[DerivationInfo])): JsObject = info._2 match {
    case Some(comfort) =>
      JsObject(
        "standardDerivation" -> derivationJson(info._1),
        "comfortDerivation" -> derivationJson(comfort),
        "positionSuggestion" -> posJson(suggestedPosition)
      )
    case None =>
      JsObject(
        "standardDerivation" -> derivationJson(info._1),
        "positionSuggestion" -> posJson(suggestedPosition)
      )
  }

  def getJson: JsValue = JsArray(derivationInfos.map(derivationJson):_*)
}

case class ApplicableDefinitionsResponse(defs: List[(NamedSymbol, Expression, Option[Expression], Boolean)]) extends Response {
  /** Transforms name `n`, its expression `ne`, and its replacement `re`. */
  private def getDefJson(n: NamedSymbol, ne: Expression, re: Option[Expression], isEditable: Boolean): JsValue = {
    JsObject(
      "symbol" -> JsString(n match {
        case SystemConst(n, _) => n
        case _ => n.prettyString
      }),
      "definition" -> JsObject(
        "what" -> JsString(ne match {
          case SystemConst(n, _) => n
          case _ => ne.prettyString
        }),
        "repl" -> JsString(re.map(_.prettyString).getOrElse("")),
        "editable" -> JsBoolean(isEditable),
        "assumptionsCart" -> JsBoolean(n.name.startsWith("A_"))
      )
    )
  }

  def getJson: JsValue = JsArray(defs.map(d => getDefJson(d._1, d._2, d._3, d._4)):_*)
}

class PruneBelowResponse(item: AgendaItem) extends Response {
  def getJson: JsObject = JsObject(
    "agendaItem" -> Helpers.itemJson(item)._2
  )
}

class CounterExampleResponse(kind: String, fml: Formula = True, cex: Map[NamedSymbol, Expression] = Map()) extends Response {
  def getJson: JsObject = {
    val bv = StaticSemantics.boundVars(fml).toSet[NamedSymbol]
    val (boundCex, freeCex) = cex.partition(e => bv.contains(e._1))
    JsObject(
      "result" -> JsString(kind),
      "origFormula" -> JsString(fml.prettyString.replaceAllLiterally("()", "")),
      "cexFormula" -> JsString(createCexFormula(fml, cex).replaceAllLiterally("()", "")),
      "cexValues" -> JsArray(
        freeCex.map(e => JsObject(
          "symbol" -> JsString(e._1.prettyString.replaceAllLiterally("()", "")),
          "value" -> JsString(e._2.prettyString.replaceAllLiterally("()", "")))
        ).toList:_*
      ),
      "speculatedValues" -> JsArray(
        boundCex.map(e => JsObject(
          "symbol" -> JsString(e._1.prettyString.replaceAllLiterally("()", "")),
          "value" -> JsString(e._2.prettyString.replaceAllLiterally("()", "")))
        ).toList:_*
      )
    )
  }

  private def createCexFormula(fml: Formula, cex: Map[NamedSymbol, Expression]): String = {
    def replaceWithCexVals(fml: Formula, cex: Map[NamedSymbol, Expression]): Formula = {
      ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
        override def preT(p: PosInExpr, t: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = t match {
          case v: Variable if cex.contains(v) => Right(cex(v).asInstanceOf[Term])
          case FuncOf(fn, _) if cex.contains(fn) => Right(cex(fn).asInstanceOf[Term])
          case _ => Left(None)
        }

        override def preF(p: PosInExpr, f: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = f match {
          case PredOf(fn, _) =>
            if (cex.contains(fn)) Right(cex(fn).asInstanceOf[Formula])
            else Left(None)
          case _ => Left(None)
        }
      }, fml).get
    }

    if (cex.nonEmpty & cex.forall(_._2.isInstanceOf[Term])) {
      val Imply(assumptions, conclusion) = fml

      //@note flag false comparison formulas `cmp` with (cmp<->false)
      val cexConclusion = ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
        private def makeSeq(fml: Formula): Sequent = Sequent(immutable.IndexedSeq(), immutable.IndexedSeq(fml))

        override def preF(p: PosInExpr, f: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = f match {
          case cmp: ComparisonFormula =>
            val cexCmp = TactixLibrary.proveBy(replaceWithCexVals(cmp, cex), TactixLibrary.RCF)
            if (cexCmp.subgoals.size > 1 || cexCmp.subgoals.headOption.getOrElse(makeSeq(True)) == makeSeq(False)) {
              Right(And(False, And(cmp, False)))
            } else Right(cmp)
          case _ => Left(None)
        }
      }, conclusion).get

      val cexFml = UIKeYmaeraXPrettyPrinter.htmlEncode(Imply(assumptions, cexConclusion).prettyString)

      //@note look for variables at word boundary (do not match in the middle of other words, do not match between &;)
      val symMatcher = s"(${cex.keySet.map(_.prettyString).mkString("|")})(?![^&]*;)\\b".r("v")
      val cexFmlWithVals = symMatcher.replaceAllIn(cexFml, (m: Match) => {
        val cexSym = UIKeYmaeraXPrettyPrinter.htmlEncode(m.group("v"))
        if ((m.before + cexSym).endsWith("false")) {
          cexSym
        } else {
          val cexVal = UIKeYmaeraXPrettyPrinter.htmlEncode(cex.find(_._1.prettyString == cexSym).get._2.prettyString)
          s"""<div class="k4-cex-fml"><ul><li>$cexVal</li></ul>$cexSym</div>"""
        }
      })

      //@note look for (false & cexCmp & false) groups and replace with boldface danger spans
      val cexMatcher = "false&and;(.*?)&and;false".r("fml")
      cexMatcher.replaceAllIn(cexFmlWithVals, (m: Match) => {
        val cexCmp = m.group("fml")
        s"""<div class="k4-cex-highlight text-danger">$cexCmp</div>"""
      })
    } else {
      replaceWithCexVals(fml, cex).prettyString
    }
  }
}

class ODEConditionsResponse(sufficient: List[Formula], necessary: List[Formula]) extends Response {
  //@todo formula JSON with HTML formatting in UI
  override def getJson: JsValue = JsObject(
    "sufficient" -> JsArray(sufficient.map(f => JsObject("text" -> JsString(f.prettyString))).toVector),
    "necessary" -> JsArray(necessary.map(f => JsObject("text" -> JsString(f.prettyString))).toVector)
  )
}

class PegasusCandidatesResponse(candidates: Seq[Either[Seq[(Formula, String)],Seq[(Formula, String)]]]) extends Response {
  //@todo formula JSON with HTML formatting in UI
  override def getJson: JsValue = JsObject(
    "candidates" -> JsArray(candidates.map({
      case Left(invs) => JsObject(
        "fmls" -> JsArray(invs.map(f => JsObject("text" -> JsString(f._1.prettyString), "method" -> JsString(f._2))).toVector),
        "isInv" -> JsBoolean(true))
      case Right(invs) => JsObject(
        "fmls" -> JsArray(invs.map(f => JsObject("text" -> JsString(f._1.prettyString), "method" -> JsString(f._2))).toVector),
        "isInv" -> JsBoolean(false))
    }).toVector)
  )
}

class SetupSimulationResponse(initial: Formula, stateRelation: Formula) extends Response {
  def getJson: JsValue = JsObject(
    "initial" -> JsString(initial.prettyString),
    "stateRelation" -> JsString(stateRelation.prettyString)
  )
}

class SimulationResponse(simulation: List[List[Map[NamedSymbol, Number]]], stepDuration: Term) extends Response {
  def getJson: JsObject = {
    val seriesList = simulation.map(convertToDataSeries)
    JsObject(
      "varNames" -> JsArray(seriesList.head.map(_._1).map(name => JsString(name.prettyString)).toVector),
      "ticks" -> JsArray(seriesList.head.head._2.indices.map(i => JsString(i.toString)).toVector),
      "lineStates" -> JsArray(seriesList.map(series =>
        JsArray(series.map({
          case (_, vs) => JsArray(vs.map(v => JsNumber(v.value)).toVector)
        }).toVector)).toVector),
      "radarStates" -> JsArray(simulation.map(run => JsArray(run.map(state =>
        JsArray(state.map({case (_, v) => JsNumber(v.value)}).toVector)).toVector)).toVector)
    )
  }

  def convertToDataSeries(sim: List[Map[NamedSymbol, Number]]): List[(NamedSymbol, List[Number])] = {
    // convert to data series
    val dataSeries: Map[NamedSymbol, ListBuffer[Number]] = sim.head.keySet.map(_ -> ListBuffer[Number]()).toMap
    sim.foreach(state => state.foreach({
      case (n, v) => dataSeries.getOrElse(n, throw new IllegalStateException("Unexpected data series " + n)) += v
    }))
    dataSeries.mapValues(_.toList).toList
  }
}

class KyxConfigResponse(kyxConfig: String) extends Response {
  def getJson: JsValue = JsObject(
    "kyxConfig" -> JsString(kyxConfig)
  )
}

class KeymaeraXVersionResponse(installedVersion: String, upToDate: Option[Boolean], latestVersion: Option[String]) extends Response {
  assert(upToDate.isDefined == latestVersion.isDefined, "upToDate and latestVersion should both be defined, or both be undefined.")
  def getJson: JsObject = upToDate match {
    case Some(b) if b => JsObject("keymaeraXVersion" -> JsString(installedVersion), "upToDate" -> JsTrue)
    case Some(b) if !b => JsObject("keymaeraXVersion" -> JsString(installedVersion), "upToDate" -> JsFalse, "latestVersion" -> JsString(latestVersion.get))
    case None => JsObject("keymaeraXVersion" -> JsString(installedVersion))
  }
}

class ConfigureMathematicaResponse(linkNamePrefix: String, jlinkLibDirPrefix: String, success: Boolean) extends Response {
  def getJson: JsValue = JsObject(
    "linkNamePrefix" -> JsString(linkNamePrefix),
    "jlinkLibDirPrefix" -> JsString(jlinkLibDirPrefix),
    "success" -> {if(success) JsTrue else JsFalse}
  )
}

class ConfigureZ3Response(z3Path: String, success: Boolean) extends Response {
  def getJson: JsValue = JsObject(
    "z3Path" -> JsString(z3Path),
    "success" -> { if(success) JsTrue else JsFalse }
  )
}

class MathematicaConfigSuggestionResponse(os: String, jvmBits: String, suggestionFound: Boolean,
                                          suggestion: ToolConfiguration.ConfigSuggestion,
                                          allSuggestions: List[ToolConfiguration.ConfigSuggestion]) extends Response {

  private def convertSuggestion(info: ToolConfiguration.ConfigSuggestion): JsValue = JsObject(
    "version" -> JsString(info.version),
    "kernelPath" -> JsString(info.kernelPath),
    "kernelName" -> JsString(info.kernelName),
    "jlinkPath" -> JsString(info.jlinkPath),
    "jlinkName" -> JsString(info.jlinkName)
  )

  def getJson: JsValue = JsObject(
    "os" -> JsString(os),
    "jvmArchitecture" -> JsString(jvmBits),
    "suggestionFound" -> JsBoolean(suggestionFound),
    "suggestion" -> convertSuggestion(suggestion),
    "allSuggestions" -> JsArray(allSuggestions.map(convertSuggestion):_*)
  )
}

class Z3ConfigSuggestionResponse(defaultPath: String) extends Response {
  def getJson: JsValue = JsObject("z3Path" -> JsString(defaultPath))
}

//@todo these are a mess.
class SystemInfoResponse(os: String, osVersion: String, jvmHome: String, jvmVendor: String,
                         jvmVersion: String, jvmBits: String) extends Response {
  def getJson: JsValue = JsObject(
    "os" -> JsString(os),
    "osVersion" -> JsString(osVersion),
    "jvmHome" -> JsString(jvmHome),
    "jvmVendor" -> JsString(jvmVendor),
    "jvmVersion" -> JsString(jvmVersion),
    "jvmArchitecture" -> JsString(jvmBits)
  )
}

class MathematicaConfigurationResponse(linkName: String, jlinkLibDir: String, jlinkTcpip: String) extends Response {
  def getJson: JsValue = JsObject(
    "linkName" -> JsString(linkName),
    "jlinkLibDir" -> JsString(jlinkLibDir),
    "jlinkTcpip" -> JsString(jlinkTcpip)
  )
}

class Z3ConfigurationResponse(z3Path: String) extends Response {
  def getJson: JsValue = JsObject(
    "z3Path" -> JsString(z3Path)
  )
}

class FullConfigurationResponse(content: String) extends Response {
  override def getJson: JsValue = JsObject(
    "content" -> JsString(content)
  )
}

class ToolConfigStatusResponse(tool: String, configured: Boolean) extends Response {
  def getJson: JsValue = JsObject(
    "tool" -> JsString(tool),
    "configured" -> { if (configured) JsTrue else JsFalse }
  )
}

class ToolStatusResponse(tool: String, availableWorkers: Int) extends Response {
  def getJson: JsValue = JsObject(
    "tool" -> JsString(tool),
    "busy" -> JsBoolean(availableWorkers <= 0),
    "availableWorkers" -> JsNumber(availableWorkers)
  )
}

class ListExamplesResponse(examples: List[ExamplePOJO]) extends Response {
  def getJson: JsValue = JsArray(
    examples.map(e =>
      JsObject(
        "id" -> JsNumber(e.id),
        "title" -> JsString(e.title),
        "description" -> JsString(e.description),
        "infoUrl" -> JsString(e.infoUrl),
        "url" -> JsString(e.url),
        "image" -> JsString(e.imageUrl)
      )
    ).toVector
  )
}

class GetTemplatesResponse(templates: List[TemplatePOJO]) extends Response {
  def getJson: JsValue = JsArray(
    templates.map(t =>
      JsObject(
        "title" -> JsString(t.title),
        "description" -> JsString(t.description),
        "text" -> JsString(t.text),
        "selectRange" -> t.selectRange.map(r => JsObject(
          "start" -> JsObject("row" -> JsNumber(r.line), "column" -> JsNumber(r.column)),
          "end" -> JsObject("row" -> JsNumber(r.endLine), "column" -> JsNumber(r.endColumn))
        )).getOrElse(JsNull),
        "imageUrl" -> t.imageUrl.map(JsString(_)).getOrElse(JsNull)
      )
    ).toVector
  )
}

class GetControlledStabilityTemplateResponse(code: String, switched: SwitchedSystem, specKind: List[String]) extends Response {
  private val prg = switched.asProgram
  private val printer = new KeYmaeraXPrettierPrinter(80)
  private val fmls = specKind.map({
    case s@"stability" => s -> printer(SwitchedSystems.stabilitySpec(switched)).linesWithSeparators.zipWithIndex.map({ case (l,i) => if (i == 0) l else "  " + l}).mkString
    case s@"attractivity" => s -> printer(SwitchedSystems.attractivitySpec(switched)).linesWithSeparators.zipWithIndex.map({ case (l,i) => if (i == 0) l else "  " + l}).mkString
    case s@"custom" =>
      s -> s"""true /* todo */ ->
              |  [ ${printer(prg).linesWithSeparators.zipWithIndex.map({ case (l,i) => if (i == 0) l else "    " + l}).mkString}
              |  ]false /* todo */
              |""".stripMargin
  })
  private val entries = fmls.map({ case (s, fml) =>
    s"""ArchiveEntry "New Entry: $s"
       |/*
       | * Generated from hybrid automaton
       | * ${code.linesWithSeparators.zipWithIndex.map({ case (l, i) => if (i == 0) l else " * " + l }).mkString}
       | */
       |
       |Definitions
       |  ${definitionsContent(prg)}
       |End.
       |
       |ProgramVariables
       |  ${programVariablesContent(prg)}
       |End.
       |
       |Problem
       |  $fml
       |End.
       |
       |End.
       |""".stripMargin}).mkString("\n\n")

  def getJson: JsValue = JsObject(
    "title" -> JsString(""),
    "description" -> JsString(""),
    "text" -> JsString(entries),
    "selectRange" -> JsObject(),
    "imageUrl" -> JsNull //@todo automaton SVG?
  )

  private def definitionsContent(prg: Program): String = {
    val consts = StaticSemantics.symbols(prg) -- StaticSemantics.boundVars(prg).toSet
    val (m, c) = consts.partition(s => switched.modeNames.contains(s.prettyString))
    m.toList.sortBy(_.prettyString).zipWithIndex.map({ case (v, i) => v.sort.toString + " " + v.prettyString + " = " + i + ";" }).mkString("\n  ") +
      c.map(v => v.sort.toString + " " + v.prettyString + ";").mkString("\n  ")
  }

  private def programVariablesContent(prg: Program): String = {
    StaticSemantics.boundVars(prg).toSet[Variable].filter(_.isInstanceOf[BaseVariable]).map(v => v.sort.toString + " " + v.prettyString + ";").mkString("\n  ")
  }
}


/**
 * @return JSON that is directly usable by angular.treeview
 */
class AngularTreeViewResponse(tree: String) extends Response {
  override val schema: Option[String] = Some("angular.treeview.js")

  def getJson: JsValue = JsArray( convert(JsonParser(tree).asJsObject) )

  private def convert(node: JsObject) : JsValue = {
    //TODO switch to Jolt (https://github.com/bazaarvoice/jolt) once they can handle trees
    val children = (node.fields.get("children") match {
      case Some(c) => c
      case None => throw new IllegalArgumentException("Schema violation")
    }) match {
      case JsArray(c) => c
      case _ => throw new IllegalArgumentException("Schema violation")
    }
    val proofInfo = node.fields.get("infos") match {
      case Some(info) => info
      case None => JsArray()
    }

    val id = node.fields.get("id") match { case Some(i) => i case None => throw new IllegalArgumentException("Schema violation") }
    if (children.nonEmpty) {
      // TODO only retrieves the first alternative of the bipartite graph
      val step = children.head.asJsObject
      val rule = step.fields.get("rule") match {
        case Some(r) => r.asJsObject.fields.get("name") match {
          case Some(n) => n
          case None => throw new IllegalArgumentException("Schema violation")
        }
        case None => throw new IllegalArgumentException("Schema violation")
      }
      val subgoals = step.fields.get("children") match {
        case Some(gl) => gl.asInstanceOf[JsArray].elements.map(g => convert(g.asJsObject()))
        case None => throw new IllegalArgumentException("Schema violation")
      }
      JsObject(
        "id" -> id,
        "label" -> rule,
        "info" -> proofInfo,
        "children" -> JsArray(subgoals)
      )
    } else {
      JsObject(
        "id" -> id,
        "label" -> JsString("Open Goal"), // TODO only if the goal is closed, which is not yet represented in JSON
        "info" -> proofInfo,
        "children" -> JsArray()
      )
    }
  }
}


class DashInfoResponse(openProofs: Int, allModels: Int, provedModels: Int) extends Response {
  override val schema: Option[String] = Some("DashInfoResponse.js")
  def getJson: JsValue = JsObject(
    "open_proof_count" -> JsNumber(openProofs),
    "all_models_count" -> JsNumber(allModels),
    "proved_models_count" -> JsNumber(provedModels)
  )
}

class ExtractDatabaseResponse(path: String) extends Response {
  def getJson: JsValue = JsObject(
    "path" -> JsString(path)
  )
}

class NodeResponse(tree: String) extends Response {
  //todo add schema.
  val node: JsObject = JsonParser(tree).asJsObject
  def getJson: JsObject = node
}


case class GetTacticResponse(tacticText: String, nodesByLoc: Map[Location, String]) extends Response {
  private def locJson(l: Location) = l match {
    case Region(l, c, el, ec) => JsObject(
      "line" -> JsNumber(l),
      "column" -> JsNumber(c),
      "endLine" -> JsNumber(el),
      "endColumn" -> JsNumber(ec)
    )
    case _ => throw new IllegalArgumentException("Unknown location kind " + l.getClass)
  }
  private def nodeByLoc(l: Location, n: String) = JsObject(
    "loc" -> locJson(l),
    "node" -> JsString(n)
  )
  def getJson: JsValue = JsObject(
    "tacticText" -> JsString(tacticText),
    "nodesByLocation" -> JsArray(nodesByLoc.map({ case (k,v) => nodeByLoc(k, v) }).toVector)
  )
}

case class ExpandTacticResponse(detailsProofId: Int, goalSequents: List[Sequent], backendGoals: List[Option[(String, String)]],
                                tacticParent: String, stepsTactic: String,
                                tree: List[ProofTreeNode], openGoals: List[AgendaItem],
                                marginLeft: Int, marginRight: Int) extends Response {
  private lazy val proofTree = {
    val theNodes: List[(String, JsValue)] = nodesJson(tree, marginLeft, marginRight, printAllSequents=true)
    JsObject(
      "nodes" -> JsObject(theNodes.toMap),
      "root" -> JsString(tree.head.id.toString))
  }

  def getJson: JsValue = JsObject(
    "tactic" -> JsObject(
      "stepsTactic" -> JsString(stepsTactic.trim()),
      "parent" -> JsString(tacticParent)
    ),
    "detailsProofId" -> JsString(detailsProofId.toString),
    if (tree.nonEmpty) "proofTree" -> proofTree else "proofTree" -> JsObject(),
    "goalSequents" -> JsArray(goalSequents.map(g => JsString(g.toString)):_*),
    "backendGoals" -> JsArray(backendGoals.map(g =>
      if (g.nonEmpty) JsObject("mathematica" -> JsString(g.get._1), "z3" -> JsString(g.get._2))
      else JsObject()
    ):_*),
    "openGoals" -> JsObject(openGoals.map(itemJson):_*)
  )
}

class TacticDiffResponse(diff: TacticDiff.Diff) extends Response {
  def getJson: JsValue = JsObject(
    "context" -> JsString(BellePrettyPrinter(diff._1.t)),
    "replOld" -> JsArray(diff._2.map({ case (dot, repl) => JsObject("dot" -> JsString(BellePrettyPrinter(dot)), "repl" -> JsString(BellePrettyPrinter(repl))) }).toVector),
    "replNew" -> JsArray(diff._3.map({ case (dot, repl) => JsObject("dot" -> JsString(BellePrettyPrinter(dot)), "repl" -> JsString(BellePrettyPrinter(repl))) }).toVector)
  )
}

class ExtractProblemSolutionResponse(tacticText: String) extends Response {
  def getJson: JsValue = JsObject(
    "fileContents" -> JsString(tacticText)
  )
}

class ValidateProofResponse(taskId: String, proved: Option[Boolean]) extends Response {
  def getJson: JsObject = proved match {
    case Some(isProved) => JsObject(
      "uuid" -> JsString(taskId),
      "running" -> JsBoolean(false),
      "proved" -> JsBoolean(isProved)
    )
    case None => JsObject(
      "uuid" -> JsString(taskId),
      "running" -> JsBoolean(true)
    )
  }
}

class MockResponse(resourceName: String) extends Response {
  //@todo add schema
  def getJson: JsValue = scala.io.Source.fromInputStream(getClass.getResourceAsStream(resourceName)).mkString.parseJson
}
