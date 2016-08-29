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
import _root_.edu.cmu.cs.ls.keymaerax.core.{Formula, Expression}
import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.core._
import com.fasterxml.jackson.annotation.JsonValue
import edu.cmu.cs.ls.keymaerax.parser.Location
import spray.json._
import java.io.{PrintWriter, StringWriter, File}

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
    case Some(s) => {
      JsObject(
        "success" -> (if(flag) JsTrue else JsFalse),
        "type" -> JsNull,
        "errorText" -> JsString(s)
      )
    }
    case None => {
      JsObject(
        "success" -> (if(flag) JsTrue else JsFalse),
        "type" -> JsNull
      )
    }
  }
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
  println(s"POSSIBLE ATTACK: ${msg}")
  override def getJson: JsValue = new ErrorResponse(msg).getJson
}

class ErrorResponse(val msg: String, val exn: Throwable = null) extends Response {
  lazy val writer = new StringWriter
  lazy val stacktrace = if (exn != null) { exn.printStackTrace(new PrintWriter(writer)); writer.toString } else ""
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
  extends ProofStatusResponse(proofId, if(isClosed) "closed" else "open")

class ProofVerificationResponse(proofId: String, isVerified: Boolean)
  extends ProofStatusResponse(proofId, if(isVerified) "proved" else "closed")

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

class TaskResultResponse(parent: TreeNode, children: List[TreeNode], progress: Boolean = true) extends Response {
  def getJson = JsObject(
    "parent" -> JsObject(
      "id" -> Helpers.nodeIdJson(parent.id),
      "children" -> Helpers.childrenJson(children)
    ),
    "newNodes" -> JsArray(children.map(Helpers.singleNodeJson):_*),
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
  def childrenJson(children: List[TreeNode]): JsValue = JsArray(children.map({ case node => nodeIdJson(node.id) }):_*)

  def sequentJson(sequent: Sequent): JsValue = {
    var num: Int = 0
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

  def nodeJson(node: TreeNode): JsValue = {
    val id = nodeIdJson(node.id)
    val sequent = sequentJson(node.sequent)
    val children = childrenJson(node.children)
    val parentOpt = node.parent.map({ case n => nodeIdJson(n.id) })
    val parent = parentOpt.getOrElse(JsNull)
    JsObject(
      "id" -> id,
      "sequent" -> sequent,
      "children" -> children,
      "rule" -> ruleJson(node.rule),
      "parent" -> parent)
  }

  def sectionJson(section: List[String]): JsValue = {
    JsObject("path" -> new JsArray(section.map{case node => JsString(node)}))
  }

  def deductionJson(deduction: List[List[String]]): JsValue =
    JsObject("sections" -> new JsArray(deduction.map{case section => sectionJson(section)}))

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

  def ruleJson(rule: String):JsValue = {
    JsObject(
      "id" -> JsString(rule),
      "name" -> JsString(rule)
    )
  }

  def singleNodeJson(node: TreeNode): JsValue = {
    JsObject (
      "id" -> nodeIdJson(node.id),
      "sequent" -> sequentJson(node.sequent),
      "children" -> childrenJson(node.children),
      "rule" -> ruleJson(node.rule),
      "parent" -> node.parent.map({case parent => nodeIdJson(parent.id)}).getOrElse(JsNull)
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

class AgendaAwesomeResponse(tree: ProofTree) extends Response {
  import Helpers._
  override val schema = Some("agendaawesome.js")

  val proofTree = {
    val nodes = tree.leavesAndRoot.map({case node => (node.id.toString, nodeJson(node))})
    JsObject(
      "id" -> proofIdJson(tree.proofId),
      "nodes" -> new JsObject(nodes.toMap),
      "root" -> nodeIdJson(tree.root.id))
  }

  val agendaItems = JsObject(tree.leaves.map({case item => itemJson(item)}))

  def getJson =
    JsObject (
      "proofTree" -> proofTree,
      "agendaItems" -> agendaItems
    )
}

class GetAgendaItemResponse(item: AgendaItemPOJO) extends Response {
  def getJson = Helpers.agendaItemJson(item)
}

class SetAgendaItemNameResponse(item: AgendaItemPOJO) extends Response {
  def getJson = Helpers.agendaItemJson(item)
}

class ProofNodeInfoResponse(proofId: String, nodeId: Option[String], nodeJson: String) extends Response {
  def getJson = JsObject(
    "proofId" -> JsString(proofId),
    "nodeId" -> JsString(nodeId match { case Some(nId) => nId case None => "" }),
    "proofNode" -> JsonParser(nodeJson)
  )
}

class ProofTaskParentResponse (parent: TreeNode) extends Response {
  import Helpers._
  def getJson = singleNodeJson(parent)
}

class GetPathAllResponse(path: List[TreeNode], parentsRemaining: Int) extends Response {
  import Helpers._
  def getJson =
    JsObject (
      "numParentsUntilComplete" -> JsNumber(parentsRemaining),
      "path" -> new JsArray(path.map({case node => nodeJson(node)}))
    )
}

class GetBranchRootResponse(node: TreeNode) extends Response {
  def getJson = Helpers.singleNodeJson(node)
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
      case inputs => JsArray(inputs.map{case input => inputJson(input)}:_*)
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
    "ante" -> new JsArray(sequent.ante.map{case fml => JsString(fml)}.toVector),
    "succ" -> new JsArray(sequent.succ.map{case fml => JsString(fml)}.toVector),
    "isClosed" -> JsBoolean(sequent.isClosed)
    )
   json
  }

  def ruleJson(info: TacticInfo, conclusion: SequentDisplay, premises: List[SequentDisplay]): JsObject = {
    val conclusionJson = sequentJson(conclusion)
    val premisesJson = JsArray(premises.map{case sequent => sequentJson(sequent)}:_*)
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

class CounterExampleResponse(kind: String, fml: Formula = True, cex: Map[NamedSymbol, Term] = Map()) extends Response {
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

  private def createCexFormula(fml: Formula, cex: Map[NamedSymbol, Term]): Formula = {
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction {
      override def preT(p: PosInExpr, t: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = t match {
        case v: Variable => Right(cex.get(v).get)
        case FuncOf(fn, _) => Right(cex.get(fn).get)
        case tt => Right(tt)
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
class MathematicaConfigSuggestionResponse(os: String, version: String, kernelPath: String, kernelName: String,
                                          jlinkPath: String, jlinkName: String) extends Response {
  def getJson: JsValue = JsObject(
    "os" -> JsString(os),
    "version" -> JsString(version),
    "kernelPath" -> JsString(kernelPath),
    "kernelName" -> JsString(kernelName),
    "jlinkPath" -> JsString(jlinkPath),
    "jlinkName" -> JsString(jlinkName)
  )
}

class MathematicaConfigurationResponse(linkName: String, jlinkLibDir: String) extends Response {
  def getJson: JsValue = JsObject(
    "linkName" -> JsString(linkName),
    "jlinkLibDir" -> JsString(jlinkLibDir)
  )
}

class MathematicaStatusResponse(configured : Boolean) extends Response {
  def getJson: JsValue = JsObject(
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
    if (children.length > 0) {
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

class ExtractProblemSolutionResponse(tacticText: String) extends Response {
  def getJson = JsObject(
    "fileContents" -> JsString(tacticText)
  )
}

class MockResponse(resourceName: String) extends Response {
  //@todo add schema
  def getJson = scala.io.Source.fromInputStream(getClass.getResourceAsStream(resourceName)).mkString.parseJson
}
