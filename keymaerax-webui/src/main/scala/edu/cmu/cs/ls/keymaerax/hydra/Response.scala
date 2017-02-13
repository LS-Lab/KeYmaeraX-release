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

import _root_.edu.cmu.cs.ls.keymaerax.btactics._
import _root_.edu.cmu.cs.ls.keymaerax.core.{Expression, Formula}
import edu.cmu.cs.ls.keymaerax.bellerophon.{Fixed, PosInExpr, PositionLocator, TacticDiff}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXPrettyPrinter, Location}
import spray.json._
import java.io.{PrintWriter, StringWriter}

import Helpers._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter
import edu.cmu.cs.ls.keymaerax.codegen.CGenerator
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.mutable.ListBuffer


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

  def getJson: JsValue
}

class BooleanResponse(flag : Boolean, errorText: Option[String] = None) extends Response {
  override val schema = Some("BooleanResponse.js")

  def getJson = errorText match {
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
  override def getJson = JsObject(data:_*)
}

class ModelListResponse(models : List[ModelPOJO]) extends Response {
  val objects = models.map(modelpojo => JsObject(
    "id" -> JsString(modelpojo.modelId.toString),
    "name" -> JsString(modelpojo.name),
    "date" -> JsString(modelpojo.date),
    "description" -> JsString(modelpojo.description),
    "pubLink" -> JsString(modelpojo.pubLink),
    "keyFile" -> JsString(modelpojo.keyFile),
    "title" -> JsString(modelpojo.title),
    "hasTactic" -> JsBoolean(modelpojo.tactic.isDefined),
    "numProofs" -> JsNumber(modelpojo.numProofs)
  ))

  def getJson = JsArray(objects:_*)
}

class UpdateProofNameResponse(proofId : String, newName : String) extends Response {
  def getJson = JsArray()
}

/**
 *
 * @param proofs The list of proofs with their status in KeYmaera (proof, loadStatus).
 * @param models -- optionally, a list of model names associated with each of the proofs in <em>proofs</em>
 */
class ProofListResponse(proofs : List[(ProofPOJO, String)], models : Option[List[String]] = None) extends Response {
  override val schema = Some("prooflist.js")

  val objects : List[JsObject] = models match {
    case None => proofs.map({case (proof, loadStatus) => JsObject(
      "id" -> JsString(proof.proofId.toString),
      "name" -> JsString(proof.name),
      "description" -> JsString(proof.description),
      "date" -> JsString(proof.date),
      "modelId" -> JsString(proof.modelId.toString),
      "stepCount" -> JsNumber(proof.stepCount),
      "status" -> JsBoolean(proof.closed),
      "loadStatus" -> JsString(loadStatus)
    )})
    case Some(modelNames) =>
      (proofs zip modelNames).map({case (p,loadStatus) =>
        val proof = p._1
        val modelName = p._2

        JsObject(
          "id" -> JsString(proof.proofId.toString),
          "name" -> JsString(proof.name),
          "description" -> JsString(proof.description),
          "date" -> JsString(proof.date),
          "modelId" -> JsString(proof.modelId.toString),
          "stepCount" -> JsNumber(proof.stepCount),
          "status" -> JsBoolean(proof.closed),
          "loadStatus" -> JsString(loadStatus),
          "modelName" -> JsString(modelName)
        )
      })
  }

  def getJson = JsArray(objects:_*)
}

class GetModelResponse(model : ModelPOJO) extends Response {
  def getJson = JsObject(
    "id" -> JsString(model.modelId.toString),
    "name" -> JsString(model.name),
    "date" -> JsString(model.date),
    "description" -> JsString(model.description),
    "pubLink" -> JsString(model.pubLink),
    "keyFile" -> JsString(model.keyFile),
    "title" -> JsString(model.title),
    "hasTactic" -> JsBoolean(model.tactic.isDefined),
    "tactic" -> JsString(model.tactic.getOrElse(""))
  )
}

class GetModelTacticResponse(model : ModelPOJO) extends Response {
  def getJson = JsObject(
    "modelId" -> JsString(model.modelId.toString),
    "modelName" -> JsString(model.name),
    "tacticBody" -> JsString(model.tactic.getOrElse(""))
  )
}

class ModelPlexMandatoryVarsResponse(model: ModelPOJO, vars: Set[Variable]) extends Response {
  def getJson = JsObject(
    "modelid" -> JsString(model.modelId.toString),
    "mandatoryVars" -> JsArray(vars.map(v => JsString(v.prettyString)).toVector)
  )
}

class ModelPlexResponse(model: ModelPOJO, monitor: Formula) extends Response {
  val fmlHtml = JsString(UIKeYmaeraXPrettyPrinter("", plainText=false)(monitor))
  val fmlString = JsString(UIKeYmaeraXPrettyPrinter("", plainText=true)(monitor))
  val fmlPlainString = JsString(KeYmaeraXPrettyPrinter(monitor))

  def getJson = JsObject(
    "modelid" -> JsString(model.modelId.toString),
    "monitor" -> JsObject(
      "html" -> fmlHtml,
      "string" -> fmlString,
      "plainString" -> fmlPlainString
    )
  )
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

  def getJson = JsObject(
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

class ModelPlexCCodeResponse(model: ModelPOJO, monitor: Formula) extends Response {
  def getJson = JsObject(
    "modelid" -> JsString(model.modelId.toString),
    "modelname" -> JsString(model.name),
    "code" -> JsString(CGenerator(monitor))
  )
}

class LoginResponse(flag:Boolean, userId:String, sessionToken : Option[String]) extends Response {
  def getJson = JsObject(
    "success" -> (if(flag) JsTrue else JsFalse),
    "sessionToken" -> (if(flag && sessionToken.isDefined) JsString(sessionToken.get) else JsFalse),
    "key" -> JsString("userId"),
    "value" -> JsString(userId),
    "type" -> JsString("LoginResponse")
  )
}

class CreatedIdResponse(id : String) extends Response {
  def getJson = JsObject("id" -> JsString(id))
}

class PossibleAttackResponse(val msg: String) extends Response {
  println(s"POSSIBLE ATTACK: $msg")
  override def getJson: JsValue = new ErrorResponse(msg).getJson
}

class ErrorResponse(val msg: String, val exn: Throwable = null) extends Response {
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
  def getJson = JsObject(
    "textStatus" -> (if (msg != null) JsString(msg) else JsString("")),
    "errorThrown" -> JsString(stacktrace),
    "type" -> JsString("error")
  )
}

class KvpResponse(val key: String, val value: String) extends Response {
  override def getJson: JsValue = JsObject(key -> JsString(value))
}

class ParseErrorResponse(msg: String, expect: String, found: String, detailedMsg: String, loc: Location, exn: Throwable = null) extends ErrorResponse(msg, exn) {
  override def getJson = JsObject(super.getJson.fields ++ Map(
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

class TacticErrorResponse(msg: String, tacticMsg: String, exn: Throwable = null) extends ErrorResponse(msg, exn) {
  override def getJson = JsObject(super.getJson.fields ++ Map(
    "tacticMsg" -> JsString(tacticMsg)
  ))
}

class GenericOKResponse() extends Response {
  def getJson = JsObject(
    "success" -> JsTrue
  )
}

class UnimplementedResponse(callUrl : String) extends ErrorResponse("Call unimplemented: " + callUrl) {}

class ProofStatusResponse(proofId: String, status: String, error: Option[String] = None) extends Response {
  override val schema = Some("proofstatus.js")
  def getJson = JsObject(
    "proofId" -> JsString(proofId),
    "type" -> JsString("ProofLoadStatus"),
    "status" -> JsString(status),
    "textStatus" -> JsString(status + ": " + proofId),
    "errorThrown" -> JsString(error.getOrElse(""))
  )
}
class ProofIsLoadingResponse(proofId : String) extends ProofStatusResponse(proofId, "loading")
class ProofNotLoadedResponse(proofId : String) extends ProofStatusResponse(proofId, "notloaded")
class ProofIsLoadedResponse(proofId: String) extends ProofStatusResponse(proofId, "loaded")
// progress "open": open goals
// progress "closed": no open goals but not checked for isProved
class ProofProgressResponse(proofId: String, isClosed: Boolean)
  extends ProofStatusResponse(proofId, if (isClosed) "closed" else "open")

class ProofVerificationResponse(proofId: String, provable: ProvableSig, tactic: String) extends Response {
  override def getJson = JsObject(
    "proofId" -> JsString(proofId),
    "isProved" -> JsBoolean(provable.isProved),
    "provable" -> JsString(provable.toString),
    "tactic" -> JsString(tactic))
}

class GetProblemResponse(proofid:String, tree:String) extends Response {
  def getJson = JsObject(
    "proofid" -> JsString(proofid),
    "proofTree" -> JsonParser(tree)
  )
}

class RunBelleTermResponse(proofId: String, nodeId: String, taskId: String) extends Response {
  def getJson = JsObject(
    "proofId" -> JsString(proofId),
    "nodeId" -> JsString(nodeId),
    "taskId" -> JsString(taskId),
    "type" -> JsString("runbelleterm")
  )
}

class TaskStatusResponse(proofId: String, nodeId: String, taskId: String, status: String, lastStep: Option[ExecutionStepPOJO]) extends Response {
  def getJson =
    if (lastStep.isDefined) JsObject(
      "proofId" -> JsString(proofId),
      "parentId" -> JsString(nodeId),
      "taskId" -> JsString(taskId),
      "status" -> JsString(status),
      "lastStep" -> JsObject(
        "ruleName" -> JsString(lastStep.get.ruleName),
        "stepStatus" -> JsString(lastStep.get.status.toString)
      ),
      "type" -> JsString("taskstatus"))
    else JsObject(
      "proofId" -> JsString(proofId),
      "parentId" -> JsString(nodeId),
      "taskId" -> JsString(taskId),
      "status" -> JsString(status),
      "type" -> JsString("taskstatus"))
}

class TaskResultResponse(proofId: String, parent: TreeNode, children: List[TreeNode], pos: Option[PositionLocator], progress: Boolean = true) extends Response {
  def getJson = JsObject(
    "proofId" -> JsString(proofId),
    "parent" -> JsObject(
      "id" -> nodeIdJson(parent.id),
      "children" -> childrenJson(children)
    ),
    "newNodes" -> JsArray(children.map(singleNodeJson(pos)):_*),
    "progress" -> JsBoolean(progress),
    "type" -> JsString("taskresult")
  )
}

class UpdateResponse(update: String) extends Response {
  def getJson = JsObject(
    "type" -> JsString("update"),
    "events" -> JsonParser(update)
  )
}

class ProofTreeResponse(tree: String) extends Response {
  def getJson = JsObject(
    "type" -> JsString("proof"),
    "tree" -> JsonParser(tree)
  )
}

class OpenProofResponse(proof : ProofPOJO, loadStatus : String) extends Response {
  override val schema = Some("proof.js")
  def getJson = JsObject(
    "id" -> JsString(proof.proofId.toString),
    "name" -> JsString(proof.name),
    "description" -> JsString(proof.description),
    "date" -> JsString(proof.date),
    "modelId" -> JsString(proof.modelId.toString),
    "stepCount" -> JsNumber(proof.stepCount),
    "status" -> JsBoolean(proof.closed),
    "loadStatus" -> JsString(loadStatus)
  )
}

class ProofAgendaResponse(tasks : List[(ProofPOJO, String, String)]) extends Response {
  override val schema = Some("proofagenda.js")
  val objects = tasks.map({ case (proofPojo, nodeId, nodeJson) => JsObject(
    "proofId" -> JsString(proofPojo.proofId.toString),
    "nodeId" -> JsString(nodeId),
    "proofNode" -> JsonParser(nodeJson)
  )})

  def getJson = JsArray(objects:_*)
}

/** JSON conversions for frequently-used response formats */
object Helpers {
  def childrenJson(children: List[TreeNode]): JsValue = JsArray(children.map(node => nodeIdJson(node.id)):_*)

  def sequentJson(sequent: Sequent): JsValue = {
    def fmlsJson (isAnte:Boolean, fmls: IndexedSeq[Formula]): JsValue = {
      JsArray(fmls.zipWithIndex.map { case (fml, i) =>
        /* Formula ID is formula number followed by comma-separated PosInExpr.
         formula number = strictly positive if succedent, strictly negative if antecedent, 0 is never used
        */
        val idx = if (isAnte) (-i)-1 else i+1
        val fmlHtml = JsString(UIKeYmaeraXPrettyPrinter(idx.toString, plainText=false)(fml))
        val fmlString = JsString(UIKeYmaeraXPrettyPrinter(idx.toString, plainText=true)(fml))
        JsObject(
          "id" -> JsString(idx.toString),
          "formula" -> JsObject(
            "html" -> fmlHtml,
            "string" -> fmlString
          )
        )}.toVector)
    }
    JsObject(
      "ante" -> fmlsJson(isAnte = true, sequent.ante),
      "succ" -> fmlsJson(isAnte = false, sequent.succ)
    )
  }

  def nodeJson(node: TreeNode, pos: Option[PositionLocator]): JsValue = {
    val id = nodeIdJson(node.id)
    val sequent = sequentJson(node.sequent)
    val children = childrenJson(node.children)
    val parentOpt = node.parent.map(n => nodeIdJson(n.id))
    val parent = parentOpt.getOrElse(JsNull)
    JsObject(
      "id" -> id,
      "sequent" -> sequent,
      "children" -> children,
      "rule" -> ruleJson(node.rule, pos),
      "parent" -> parent)
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

  def nodeIdJson(n: Int):JsValue = JsString(n.toString)
  def proofIdJson(n: String):JsValue = JsString(n)

  def ruleJson(ruleName: String, pos: Option[PositionLocator]):JsValue = {
    JsObject(
      "id" -> JsString(ruleName),
      "name" -> JsString(ruleName),
      "pos" -> (pos match {
        case Some(Fixed(p, _, _)) => JsString(p.prettyString)
        case _ => JsString("")
      })
    )
  }

  def singleNodeJson(pos: Option[PositionLocator] = None)(node: TreeNode): JsValue = {
    JsObject (
      "id" -> nodeIdJson(node.id),
      "sequent" -> sequentJson(node.sequent),
      "children" -> childrenJson(node.children),
      "rule" -> ruleJson(node.rule, pos),
      "parent" -> node.parent.map(parent => nodeIdJson(parent.id)).getOrElse(JsNull)
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

class AgendaAwesomeResponse(proofId: String, root: TreeNode, leaves: List[(TreeNode, Option[PositionLocator])],
                            agenda: List[AgendaItem], closed: Boolean) extends Response {
  override val schema = Some("agendaawesome.js")

  val proofTree = {
    //@todo position locator
    val theNodes: List[(String, JsValue)] = ((root, None) +: leaves).map(n => (n._1.id.toString, nodeJson(n._1, n._2)))
    JsObject(
      "id" -> proofIdJson(proofId),
      "nodes" -> JsObject(theNodes.toMap),
      "root" -> nodeIdJson(root.id))
  }

  val agendaItems = JsObject(agenda.map(itemJson):_*)

  def getJson =
    JsObject (
      "proofTree" -> proofTree,
      "agendaItems" -> agendaItems,
      "closed" -> JsBoolean(closed)
    )
}

class GetAgendaItemResponse(item: AgendaItemPOJO) extends Response {
  def getJson = agendaItemJson(item)
}

class SetAgendaItemNameResponse(item: AgendaItemPOJO) extends Response {
  def getJson = agendaItemJson(item)
}

class ProofNodeInfoResponse(proofId: String, nodeId: Option[String], nodeJson: String) extends Response {
  def getJson = JsObject(
    "proofId" -> JsString(proofId),
    "nodeId" -> JsString(nodeId match { case Some(nId) => nId case None => "" }),
    "proofNode" -> JsonParser(nodeJson)
  )
}

class ProofTaskParentResponse (parent: TreeNode, pos: Option[PositionLocator]) extends Response {
  def getJson = singleNodeJson(pos)(parent)
}

class GetPathAllResponse(path: List[(TreeNode, Option[PositionLocator])], parentsRemaining: Int) extends Response {
  import Helpers._
  def getJson =
    JsObject (
      "numParentsUntilComplete" -> JsNumber(parentsRemaining),
      "path" -> JsArray(path.map(pe => nodeJson(pe._1, pe._2)):_*)
    )
}

class GetBranchRootResponse(node: TreeNode, pos: Option[PositionLocator]) extends Response {
  def getJson = singleNodeJson(pos)(node)
}

class ApplicableAxiomsResponse(derivationInfos : List[(DerivationInfo, Option[DerivationInfo])],
                               suggestedInput: Option[Expression]) extends Response {
  def inputJson(input: ArgInfo): JsValue = {
    (suggestedInput, input) match {
      case (Some(fml), FormulaArg(name)) =>
        JsObject (
          "type" -> JsString(input.sort),
          "param" -> JsString(name),
          "value" -> JsString(fml.prettyString)
        )
      case (_, ListArg(name, elementSort)) => //@todo suggested input for Formula*
        JsObject(
          "type" -> JsString(input.sort),
          "elementType" -> JsString(elementSort),
          "param" -> JsString(name)
        )
      case _ =>
        JsObject (
          "type" -> JsString(input.sort),
          "param" -> JsString(input.name)
        )
    }
  }

  def inputsJson(info:List[ArgInfo]): JsArray = {
    info match {
      case Nil => JsArray()
      case inputs => JsArray(inputs.map(inputJson):_*)
    }
  }

  def axiomJson(info:DerivationInfo): JsObject = {
    val formulaText =
      (info, info.display) match {
        case (_, AxiomDisplayInfo(_, formulaDisplay)) => formulaDisplay
        case (_, InputAxiomDisplayInfo(_, formulaDisplay, _)) => formulaDisplay
        case (info:AxiomInfo, _) => info.formula.prettyString
      }
    JsObject (
    "type" -> JsString("axiom"),
    "formula" -> JsString(formulaText),
    "input" -> inputsJson(info.inputs)
    )
  }

  def tacticJson(info:TacticInfo): JsObject = {
    JsObject(
      "type" -> JsString("tactic"),
      "input" -> inputsJson(info.inputs)
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

  def ruleJson(info: TacticInfo, conclusion: SequentDisplay, premises: List[SequentDisplay]): JsObject = {
    val conclusionJson = sequentJson(conclusion)
    val premisesJson = JsArray(premises.map(sequentJson):_*)
    JsObject(
      "type" -> JsString("sequentrule"),
      "conclusion" -> conclusionJson,
      "premise" -> premisesJson,
      "input" -> inputsJson(info.inputs))
  }

  def derivationJson(derivationInfo: DerivationInfo): JsObject = {
    val derivation =
      derivationInfo match {
        case info:AxiomInfo => axiomJson(info)
        case info:TacticInfo =>
          info.display match {
            case _: SimpleDisplayInfo => tacticJson(info)
            case display : AxiomDisplayInfo => axiomJson(info)
            case RuleDisplayInfo(_, conclusion, premises) => ruleJson(info, conclusion, premises)
          }
      }
    JsObject(
      "id" -> new JsString(derivationInfo.codeName),
      "name" -> new JsString(derivationInfo.display.name),
      "derivation" -> derivation
    )
  }

  def derivationJson(info: (DerivationInfo, Option[DerivationInfo])): JsObject = info._2 match {
    case Some(comfort) =>
      JsObject(
        "standardDerivation" -> derivationJson(info._1),
        "comfortDerivation" -> derivationJson(comfort)
      )
    case None =>
      JsObject(
        "standardDerivation" -> derivationJson(info._1)
      )
  }

  def getJson = JsArray(derivationInfos.map(derivationJson):_*)
}
class PruneBelowResponse(item:AgendaItem) extends Response {
  def getJson = JsObject (
  "agendaItem" -> Helpers.itemJson(item)._2
  )
}

class CounterExampleResponse(kind: String, fml: Formula = True, cex: Map[NamedSymbol, Expression] = Map()) extends Response {
  def getJson = JsObject(
    "result" -> JsString(kind),
    "origFormula" -> JsString(fml.prettyString),
    "cexFormula" -> JsString(createCexFormula(fml, cex).prettyString),
    "cexValues" -> JsArray(
      cex.map(e => JsObject(
        "symbol" -> JsString(e._1.prettyString),
        "value" -> JsString(e._2.prettyString))
      ).toList:_*
    )
  )

  private def createCexFormula(fml: Formula, cex: Map[NamedSymbol, Expression]): Formula = {
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
      override def preT(p: PosInExpr, t: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = t match {
        case v: Variable => Right(cex(v).asInstanceOf[Term])
        case FuncOf(fn, _) => Right(cex(fn).asInstanceOf[Term])
        case tt => Right(tt)
      }
      override def preF(p: PosInExpr, f: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = f match {
        case PredOf(fn, _) => Right(cex(fn).asInstanceOf[Formula])
        case ff => Right(ff)
      }
    }, fml).get
  }
}

class SetupSimulationResponse(initial: Formula, stateRelation: Formula) extends Response {
  def getJson = JsObject(
    "initial" -> JsString(initial.prettyString),
    "stateRelation" -> JsString(stateRelation.prettyString)
  )
}

class SimulationResponse(simulation: List[List[Map[NamedSymbol, Number]]], stepDuration: Term) extends Response {
  def getJson = {
    val seriesList = simulation.map(convertToDataSeries)
    JsObject(
      "varNames" -> JsArray(seriesList.head.map(_._1).map(name => JsString(name.prettyString)).toVector),
      "ticks" -> JsArray(seriesList.head.head._2.indices.map(i => JsString(i.toString)).toVector),
      "lineStates" -> JsArray(seriesList.map(series =>
        JsArray(series.map({
          case (n, vs) => JsArray(vs.map(v => JsNumber(v.value)).toVector)
        }).toVector)).toVector),
      "radarStates" -> JsArray(simulation.map(run => JsArray(run.map(state =>
        JsArray(state.map({case (n, v) => JsNumber(v.value)}).toVector)).toVector)).toVector)
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
  def getJson = JsObject(
    "kyxConfig" -> JsString(kyxConfig)
  )
}

class KeymaeraXVersionResponse(installedVersion: String, upToDate: Option[Boolean], latestVersion: Option[String]) extends Response {
  assert(upToDate.isDefined == latestVersion.isDefined, "upToDate and latestVersion should both be defined, or both be undefined.")
  def getJson = upToDate match {
    case Some(b) if b => JsObject("keymaeraXVersion" -> JsString(installedVersion), "upToDate" -> JsTrue)
    case Some(b) if !b => JsObject("keymaeraXVersion" -> JsString(installedVersion), "upToDate" -> JsFalse, "latestVersion" -> JsString(latestVersion.get))
    case None => JsObject("keymaeraXVersion" -> JsString(installedVersion))
  }
}

class ConfigureMathematicaResponse(linkNamePrefix : String, jlinkLibDirPrefix : String, success : Boolean) extends Response {
  def getJson = JsObject(
    "linkNamePrefix" -> JsString(linkNamePrefix),
    "jlinkLibDirPrefix" -> JsString(jlinkLibDirPrefix),
    "success" -> {if(success) JsTrue else JsFalse}
  )
}

//@todo these are a mess.
class MathematicaConfigSuggestionResponse(os: String, jvmBits: String, suggestionFound: Boolean,
                                          version: String, kernelPath: String, kernelName: String,
                                          jlinkPath: String, jlinkName: String,
                                          allSuggestions: List[(String, String, String, String, String)]) extends Response {

  private def convertSuggestion(info: (String, String, String, String, String)): JsValue = JsObject(
    "version" -> JsString(info._1),
    "kernelPath" -> JsString(info._2),
    "kernelName" -> JsString(info._3),
    "jlinkPath" -> JsString(info._4),
    "jlinkName" -> JsString(info._5)
  )

  def getJson: JsValue = JsObject(
    "os" -> JsString(os),
    "jvmArchitecture" -> JsString(jvmBits),
    "suggestionFound" -> JsBoolean(suggestionFound),
    "suggestion" -> convertSuggestion((version, kernelPath, kernelName, jlinkPath, jlinkName)),
    "allSuggestions" -> JsArray(allSuggestions.map(convertSuggestion):_*)
  )
}

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

class MathematicaConfigurationResponse(linkName: String, jlinkLibDir: String) extends Response {
  def getJson: JsValue = JsObject(
    "linkName" -> JsString(linkName),
    "jlinkLibDir" -> JsString(jlinkLibDir)
  )
}

class ToolStatusResponse(tool: String, configured : Boolean) extends Response {
  def getJson: JsValue = JsObject(
    "tool" -> JsString(tool),
    "configured" -> {if(configured) JsTrue else JsFalse}
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


/**
 * @return JSON that is directly usable by angular.treeview
 */
class AngularTreeViewResponse(tree : String) extends Response {
  override val schema = Some("angular.treeview.js")

  def getJson = JsArray( convert(JsonParser(tree).asJsObject) )

  private def convert(node : JsObject) : JsValue = {
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


class DashInfoResponse(openProofs:Int, allModels: Int, provedModels: Int) extends Response {
  override val schema = Some("DashInfoResponse.js")
  def getJson = JsObject(
    "open_proof_count" -> JsNumber(openProofs),
    "all_models_count" -> JsNumber(allModels),
    "proved_models_count" -> JsNumber(provedModels)
  )
}

class ExtractDatabaseResponse(path: String) extends Response {
  def getJson = JsObject(
    "path" -> JsString(path)
  )
}

class NodeResponse(tree : String) extends Response {
  //todo add schema.
  val node = JsonParser(tree).asJsObject
  def getJson = node
}


class ExtractTacticResponse(tacticText: String) extends Response {
  def getJson = JsObject(
    "tacticText" -> JsString(tacticText)
  )
}

class ExpandTacticResponse(detailsProofId: Int, tacticParent: String, stepsTactic: String, tree: List[(TreeNode, Option[PositionLocator])], openGoals: List[AgendaItem]) extends Response {
  private lazy val proofTree = {
    val theNodes: List[(String, JsValue)] = tree.map(n => (n._1.id.toString, nodeJson(n._1, n._2)))
    JsObject(
      "nodes" -> JsObject(theNodes.toMap),
      "root" -> nodeIdJson(tree.head._1.id))
  }

  def getJson = JsObject(
    "tactic" -> JsObject(
      "stepsTactic" -> JsString(stepsTactic),
      "parent" -> JsString(tacticParent)
    ),
    "detailsProofId" -> JsString(detailsProofId.toString),
    if (tree.nonEmpty) "proofTree" -> proofTree else "proofTree" -> JsObject(),
    "openGoals" -> JsObject(openGoals.map(itemJson):_*)
  )
}

class TacticDiffResponse(diff: TacticDiff.Diff) extends Response {
  def getJson = JsObject(
    "context" -> JsString(BellePrettyPrinter(diff._1.t)),
    "replOld" -> JsArray(diff._2.map({ case (dot, repl) => JsObject("dot" -> JsString(BellePrettyPrinter(dot)), "repl" -> JsString(BellePrettyPrinter(repl))) }).toVector),
    "replNew" -> JsArray(diff._3.map({ case (dot, repl) => JsObject("dot" -> JsString(BellePrettyPrinter(dot)), "repl" -> JsString(BellePrettyPrinter(repl))) }).toVector)
  )
}

class ExtractProblemSolutionResponse(tacticText: String) extends Response {
  def getJson = JsObject(
    "fileContents" -> JsString(tacticText)
  )
}

class ValidateProofResponse(taskId: String, proved: Option[Boolean]) extends Response {
  def getJson = proved match {
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
  def getJson = scala.io.Source.fromInputStream(getClass.getResourceAsStream(resourceName)).mkString.parseJson
}
