/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * HyDRA API Responses
 * @author
 *   Nathan Fulton
 * @author
 *   Stefan Mitsch
 * @author
 *   Ran Ji
 */
package org.keymaerax.hydra

import org.keymaerax.infrastruct.Augmentors._
import org.keymaerax.core.{Expression, Formula}
import org.keymaerax.bellerophon._
import org.keymaerax.core._
import org.keymaerax.parser._
import org.keymaerax.Logging
import org.keymaerax.bellerophon.parser.BelleParser
import org.keymaerax.infrastruct._
import org.keymaerax.btactics.macros._
import org.keymaerax.hydra.responses.proofs.ApplicableAxiomsResponse

import spray.json._
import akka.http.scaladsl.marshalling.ToResponseMarshallable
import akka.http.scaladsl.marshallers.xml.ScalaXmlSupport._

import java.io.{PrintWriter, StringWriter}

import scala.annotation.tailrec
import scala.collection.immutable.Seq
import scala.util.Try
import scala.xml.Elem

/**
 * Responses are like views -- they shouldn't do anything except produce appropriately formatted JSON from their
 * parameters.
 *
 * To create a new response:
 *   1. Create a new object extending Response (perhaps with constructor arguments)
 *   1. override the json value with the json to be generated.
 *   1. override the schema value with Some(File(...)) containing the schema.
 *
 * See BooleanResponse for the simplest example.
 */
trait Response {

  /** Should be the name of a single file within resources/js/schema. */
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

/** Responds with dynamically generated Javascript code. */
case class JSResponse(code: String) extends Response {
  override def getJson: JsValue = throw new UnsupportedOperationException("JS response is no JSON data")
  override def print: ToResponseMarshallable = code
}

case class BooleanResponse(flag: Boolean, errorText: Option[String] = None) extends Response {
  override val schema: Option[String] = Some("BooleanResponse.js")

  def getJson: JsObject = errorText match {
    case Some(s) => JsObject("success" -> (if (flag) JsTrue else JsFalse), "type" -> JsNull, "errorText" -> JsString(s))
    case None => JsObject("success" -> (if (flag) JsTrue else JsFalse), "type" -> JsNull)
  }
}

class PlainResponse(data: (String, JsValue)*) extends Response {
  override def getJson: JsValue = JsObject(data: _*)
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
      writer
        .toString
        .replaceAll("[\\t]at spray\\.routing\\..*", "")
        .replaceAll("[\\t]at java\\.util\\.concurrent\\..*", "")
        .replaceAll("[\\t]at java\\.lang\\.Thread\\.run.*", "")
        .replaceAll("[\\t]at scala\\.Predef\\$\\.require.*", "")
        .replaceAll("[\\t]at akka\\.spray\\.UnregisteredActorRefBase.*", "")
        .replaceAll("[\\t]at akka\\.dispatch\\..*", "")
        .replaceAll("[\\t]at scala\\.concurrent\\.forkjoin\\..*", "")
        .replaceAll("[\\t]at scala\\.runtime\\.AbstractPartialFunction.*", "")
        .replaceAll("\\s+$|\\s*(\n)\\s*|(\\s)\\s*", "$1$2") // @note collapse newlines
    } else ""
  def getJson: JsValue = JsObject(
    "textStatus" -> (if (msg != null) JsString(msg.replace("[Bellerophon Runtime]", "")) else JsString("")),
    "causeMsg" ->
      (if (exn != null && exn.getMessage != null) JsString(exn.getMessage.replace("[Bellerophon Runtime", ""))
       else JsString("")),
    "errorThrown" -> JsString(stacktrace),
    "type" -> JsString(severity),
  )
}

class KvpResponse(val key: String, val value: String) extends Response {
  override def getJson: JsValue = JsObject(key -> JsString(value))
}

class GenericOKResponse() extends Response {
  def getJson: JsValue = JsObject("success" -> JsTrue)
}

class UnimplementedResponse(callUrl: String) extends ErrorResponse("Call unimplemented: " + callUrl) {}

/** JSON conversions for frequently-used response formats */
object Helpers {

  /** Stateful format provider to read off whitespace and line breaks from a pretty-printed string. */
  case class HtmlPrettyPrintFormatProvider(
      format: String,
      wsPrinter: String => String = _.replace("\n", "<br/>").replaceAll("\\s", "&nbsp;"),
  ) extends PrettyPrintFormatProvider(format, wsPrinter) {}

  /** Noop format provider. */
  class NoneFormatProvider extends FormatProvider {
    override def printWS(check: String): String = ""
    override def print(next: String): String = next
  }

  private val exprPrinter = new UIAbbreviatingKeYmaeraXPrettyPrinter

  def sequentJson(sequent: Sequent, marginLeft: Int, marginRight: Int): JsValue = {
    def fmlsJson(isAnte: Boolean, fmls: IndexedSeq[Formula]): JsValue = {
      JsArray(
        fmls
          .zipWithIndex
          .map { case (fml, i) =>
            /* Formula ID is formula number followed by comma-separated PosInExpr.
         formula number = strictly positive if succedent, strictly negative if antecedent, 0 is never used
             */
            val idx = if (isAnte) (-i) - 1 else i + 1
            val fmlString = JsString(UIKeYmaeraXPrettyPrinter(idx.toString, plainText = true)(fml))

            val format = new UIAbbreviatingKeYmaeraXPrettierPrinter(if (isAnte) marginLeft else marginRight)(fml)
            val fmlJson = printJson(PosInExpr(), fml, HtmlPrettyPrintFormatProvider(format))(Position(idx), fml)
            JsObject("id" -> JsString(idx.toString), "formula" -> JsObject("json" -> fmlJson, "string" -> fmlString))
          }
          .toVector
      )
    }
    JsObject("ante" -> fmlsJson(isAnte = true, sequent.ante), "succ" -> fmlsJson(isAnte = false, sequent.succ))
  }

  private def printObject(text: String, kind: String = "text"): JsValue =
    JsObject("text" -> JsString(text), "kind" -> JsString(kind))
  private def print(text: String, fp: FormatProvider, kind: String = "text"): JsValue =
    printObject(fp.print(text), kind)
  private def print(q: PosInExpr, text: String, kind: String, fp: FormatProvider)(implicit top: Position): JsValue =
    JsObject(
      "id" -> JsString(top.toString + (if (q.pos.nonEmpty) "," + q.pos.mkString(",") else "")),
      "text" -> JsString(fp.print(text)),
      "kind" -> JsString(kind),
    )
  private def print(
      q: PosInExpr,
      kind: String,
      hasStep: Boolean,
      isEditable: Boolean,
      plainText: => String,
      children: Seq[JsValue],
  )(implicit top: Position): JsValue = {
    JsObject(
      "id" -> JsString(top.toString + (if (q.pos.nonEmpty) "," + q.pos.mkString(",") else "")),
      "kind" -> JsString(kind),
      "plain" -> (if (isEditable || q.pos.isEmpty) JsString(plainText) else JsNull),
      "step" -> JsString(if (hasStep) "has-step" else "no-step"),
      "editable" -> JsString(if (isEditable) "editable" else "not-editable"),
      "children" -> JsArray(children: _*),
    )
  }

  private def op(expr: Expression, fp: FormatProvider, opLevel: String = "op"): JsValue = expr match {
    // terms
    case _: Minus => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&minus;", opLevel + " k4-term-op")
    case _: Neg => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&minus;", opLevel + " k4-term-op")
    case _: Term => printObject(fp.print(OpSpec.op(expr).opcode), opLevel + " k4-term-op")
    // formulas
    case _: NotEqual => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&ne;", opLevel + " k4-cmpfml-op")
    case _: GreaterEqual => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&ge;", opLevel + " k4-cmpfml-op")
    case _: Greater => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&gt;", opLevel + " k4-cmpfml-op")
    case _: LessEqual => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&le;", opLevel + " k4-cmpfml-op")
    case _: Less => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&lt;", opLevel + " k4-cmpfml-op")
    case _: Forall => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&forall;", opLevel + " k4-fml-op")
    case _: Exists => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&exist;", opLevel + " k4-fml-op")
    case _: Not => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&not;", opLevel + " k4-propfml-op")
    case _: And => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&and;", opLevel + " k4-propfml-op")
    case _: Or => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&or;", opLevel + " k4-propfml-op")
    case _: Imply => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&rarr;", opLevel + " k4-propfml-op")
    case _: Equiv => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&#8596;", opLevel + " k4-propfml-op")
    case _: Formula => printObject(fp.printWS(OpSpec.op(expr).opcode) + OpSpec.op(expr).opcode, opLevel + " k4-fml-op")
    // programs
    case _: Choice => printObject(fp.printWS(OpSpec.op(expr).opcode) + "&cup;", opLevel + " k4-prg-op")
    case _: Program => printObject(fp.printWS(OpSpec.op(expr).opcode) + OpSpec.op(expr).opcode, opLevel + " k4-prg-op")
    case _ => printObject(fp.printWS(OpSpec.op(expr).opcode) + OpSpec.op(expr).opcode, opLevel)
  }

  // @see [[KeYmaeraXPrecedencePrinter]]
  private def skipParens(expr: Modal): Boolean = OpSpec.op(expr.child) <= OpSpec.op(expr)
  private def skipParens(expr: Quantified): Boolean = OpSpec.op(expr.child) <= OpSpec.op(expr)
  private def skipParens(expr: UnaryComposite): Boolean =
    if (OpSpec.negativeNumber && expr.isInstanceOf[Term]) OpSpec.op(expr.child) <= OpSpec.op(expr) &&
    !leftMostLeaf(expr.child).exists(_.isInstanceOf[Number])
    else OpSpec.op(expr.child) <= OpSpec.op(expr)
  private def skipParensLeft(expr: BinaryComposite): Boolean = OpSpec.op(expr.left) < OpSpec.op(expr) ||
    OpSpec.op(expr.left) <= OpSpec.op(expr) &&
    OpSpec.op(expr).assoc == LeftAssociative && OpSpec.op(expr.left).assoc == LeftAssociative
  private def skipParensRight(expr: BinaryComposite): Boolean = OpSpec.op(expr.right) < OpSpec.op(expr) ||
    OpSpec.op(expr.right) <= OpSpec.op(expr) &&
    OpSpec.op(expr).assoc == RightAssociative && OpSpec.op(expr.right).assoc == RightAssociative

  private def wrapLeft(expr: BinaryComposite, left: => JsValue, fp: FormatProvider): List[JsValue] =
    if (skipParensLeft(expr)) left :: Nil else print("(", fp) :: left :: print(")", fp) :: Nil
  private def wrapRight(expr: BinaryComposite, right: => JsValue, fp: FormatProvider): List[JsValue] =
    if (skipParensRight(expr)) right :: Nil else print("(", fp) :: right :: print(")", fp) :: Nil
  private def wrapChild(expr: UnaryComposite, child: => JsValue, fp: FormatProvider): List[JsValue] =
    if (skipParens(expr)) child :: Nil else print("(", fp) :: child :: print(")", fp) :: Nil
  private def wrapChild(expr: Quantified, child: => JsValue, fp: FormatProvider): List[JsValue] =
    if (skipParens(expr)) child :: Nil else print("(", fp) :: child :: print(")", fp) :: Nil
  private def wrapChild(expr: Modal, child: => JsValue, fp: FormatProvider): List[JsValue] =
    if (skipParens(expr)) child :: Nil else print("(", fp) :: child :: print(")", fp) :: Nil
  private def pwrapLeft(expr: BinaryCompositeProgram, left: => List[JsValue], fp: FormatProvider): List[JsValue] =
    if (skipParensLeft(expr)) left else print("{", fp, "prg-open") +: left :+ print("}", fp, "prg-close")
  private def pwrapRight(expr: BinaryCompositeProgram, right: => List[JsValue], fp: FormatProvider): List[JsValue] =
    if (skipParensRight(expr)) right else print("{", fp, "prg-open") +: right :+ print("}", fp, "prg-close")

  @tailrec
  private def leftMostLeaf(t: Expression): Option[Expression] = t match {
    case _: UnaryComposite => None
    case b: BinaryComposite => leftMostLeaf(b.left)
    case x => Some(x)
  }

  private def printJson(q: PosInExpr, expr: Expression, fp: FormatProvider)(implicit
      top: Position,
      topExpr: Expression,
  ): JsValue = {
    val hasStep = UIIndex.allStepsAt(expr, Some(top ++ q), None, Nil).nonEmpty
    val parent =
      if (q.pos.isEmpty) None
      else topExpr match {
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
      case f: ComparisonFormula => print(
          q,
          "formula",
          hasStep,
          isEditable,
          exprPrinter(expr),
          wrapLeft(f, printJson(q ++ 0, f.left, fp), fp) ++ (op(f, fp) :: Nil) ++
            wrapRight(f, printJson(q ++ 1, f.right, fp), fp),
        )
      case DifferentialFormula(g) => print(
          q,
          "formula",
          hasStep,
          isEditable,
          exprPrinter(expr),
          print("(", fp) :: print(exprPrinter(g), fp) :: print(")", fp) :: op(expr, fp) :: Nil,
        )
      case f: Quantified => print(
          q,
          "formula",
          hasStep,
          isEditable,
          exprPrinter(expr),
          op(f, fp) :: print(f.vars.map(exprPrinter(_)).mkString(","), fp) ::
            Nil ++ wrapChild(f, printJson(q ++ 0, f.child, fp), fp),
        )
      case f: Box => print(
          q,
          "formula",
          hasStep,
          isEditable,
          exprPrinter(expr),
          print("[", fp, "mod-open") :: printJson(q ++ 0, f.program, fp) :: print("]", fp, "mod-close") ::
            Nil ++ wrapChild(f, printJson(q ++ 1, f.child, fp), fp),
        )
      case f: Diamond => print(
          q,
          "formula",
          hasStep,
          isEditable,
          exprPrinter(expr),
          print("<", fp, "mod-open") :: printJson(q ++ 0, f.program, fp) :: print(">", fp, "mod-close") ::
            Nil ++ wrapChild(f, printJson(q ++ 1, f.child, fp), fp),
        )
      case f: UnaryCompositeFormula => print(
          q,
          "formula",
          hasStep,
          isEditable,
          exprPrinter(expr),
          op(f, fp) +: wrapChild(f, printJson(q ++ 0, f.child, fp), fp),
        )
      case _: AtomicFormula =>
        print(q, "formula", hasStep, isEditable, exprPrinter(expr), print(exprPrinter(expr), fp) :: Nil)
      case f: BinaryCompositeFormula => print(
          q,
          "formula",
          hasStep,
          isEditable,
          exprPrinter(expr),
          wrapLeft(f, printJson(q ++ 0, f.left, fp), fp) ++ (op(f, fp) :: Nil) ++
            wrapRight(f, printJson(q ++ 1, f.right, fp), fp),
        )
      case p: Program =>
        print(q, "program", hasStep = false, isEditable = false, exprPrinter(expr), printPrgJson(q, p, fp))
      case _: Differential => print(q, exprPrinter(expr), "term", fp)
      // @note !OpSpec.negativeNumber
      case t @ Neg(Number(_)) =>
        print(q, "term", hasStep, isEditable, exprPrinter(expr), op(t, fp) :: printJson(q ++ 0, t.child, fp) :: Nil)
      case t: UnaryCompositeTerm => print(
          q,
          "term",
          hasStep,
          isEditable,
          exprPrinter(expr),
          op(t, fp) +: wrapChild(t, printJson(q ++ 0, t.child, fp), fp),
        )
      case t: BinaryCompositeTerm => print(
          q,
          "term",
          hasStep,
          isEditable,
          exprPrinter(expr),
          wrapLeft(t, printJson(q ++ 0, t.left, fp), fp) ++ (op(t, fp) :: Nil) ++
            wrapRight(t, printJson(q ++ 1, t.right, fp), fp),
        )
      case FuncOf(Function(_, _, _, _, i), _) =>
        if (i.isDefined) print(q, exprPrinter(expr), "interp-fn", fp) else print(q, exprPrinter(expr), "term", fp)
      case _ => print(q, exprPrinter(expr), "term", fp)
    }
  }

  private def printPrgJson(q: PosInExpr, expr: Program, fp: FormatProvider)(implicit
      top: Position,
      topExpr: Expression,
  ): List[JsValue] = expr match {
    case Assign(x, e) => printJson(q ++ 0, x, fp) :: op(expr, fp, "topop") :: printJson(q ++ 1, e, fp) ::
        print(";", fp) :: Nil
    case AssignAny(x) => printJson(q ++ 0, x, fp) :: op(expr, fp, "topop") :: print(";", fp) :: Nil
    case Test(f) => op(expr, fp, "topop") :: printJson(q ++ 0, f, fp) :: print(";", fp) :: Nil
    case t: UnaryCompositeProgram => print("{", fp, "prg-open") +: printRecPrgJson(q ++ 0, t.child, fp) :+
        print("}", fp, "prg-close") :+ op(t, fp, "topop")
    case t: Compose => pwrapLeft(t, printRecPrgJson(q ++ 0, t.left, fp), fp) ++
        (print(q, "", "topop k4-prg-op", fp) :: Nil) ++ pwrapRight(t, printRecPrgJson(q ++ 1, t.right, fp), fp)
    case t: BinaryCompositeProgram => pwrapLeft(t, printRecPrgJson(q ++ 0, t.left, fp), fp) ++
        (op(t, fp, "topop") :: Nil) ++ pwrapRight(t, printRecPrgJson(q ++ 1, t.right, fp), fp)
    case ODESystem(ode, f) if f != True =>
      print("{", fp, "prg-open") :: printJson(q ++ 0, ode, fp) :: print(q, "&", "topop k4-prg-op", fp) ::
        printJson(q ++ 1, f, fp) :: print("}", fp, "prg-close") :: Nil
    case ODESystem(ode, f) if f == True =>
      print("{", fp, "prg-open") :: printJson(q ++ 0, ode, fp) :: print("}", fp, "prg-close") :: Nil
    case AtomicODE(xp, e) => printJson(q ++ 0, xp, fp) :: op(expr, fp, "topop") :: printJson(q ++ 1, e, fp) :: Nil
    case t: DifferentialProduct => printJson(q ++ 0, t.left, fp) :: op(t, fp, "topop") ::
        printJson(q ++ 1, t.right, fp) :: Nil
    case c: DifferentialProgramConst => print(exprPrinter(c), fp) :: Nil
    case c: ProgramConst =>
      print(c.asString /* needs to be consistent with OpSpec.statementSemicolon (inaccessible here) */ + ";", fp) :: Nil
    case c: SystemConst =>
      print(c.asString /* needs to be consistent with OpSpec.statementSemicolon (inaccessible here) */ + ";", fp) :: Nil
  }

  private def printRecPrgJson(q: PosInExpr, expr: Program, fp: FormatProvider)(implicit
      top: Position,
      topExpr: Expression,
  ): List[JsValue] = expr match {
    case Assign(x, e) => printJson(q ++ 0, x, fp) :: op(expr, fp) :: printJson(q ++ 1, e, fp) :: print(";", fp) :: Nil
    case AssignAny(x) => printJson(q ++ 0, x, fp) :: op(expr, fp) :: print(";", fp) :: Nil
    case Test(f) => op(expr, fp) :: printJson(q ++ 0, f, fp) :: print(";", fp) :: Nil
    case t: UnaryCompositeProgram => print("{", fp, "prg-open") +: printRecPrgJson(q ++ 0, t.child, fp) :+
        print("}", fp, "prg-close") :+ op(t, fp)
    case t: Compose => pwrapLeft(t, printRecPrgJson(q ++ 0, t.left, fp), fp) ++
        pwrapRight(t, printRecPrgJson(q ++ 1, t.right, fp), fp)
    case t: BinaryCompositeProgram => pwrapLeft(t, printRecPrgJson(q ++ 0, t.left, fp), fp) ++ (op(t, fp) :: Nil) ++
        pwrapRight(t, printRecPrgJson(q ++ 1, t.right, fp), fp)
    case ODESystem(ode, f) if f != True =>
      print("{", fp, "prg-open") :: printJson(q ++ 0, ode, fp) :: print("&", fp) :: printJson(q ++ 1, f, fp) ::
        print("}", fp, "prg-close") :: Nil
    case ODESystem(ode, f) if f == True =>
      print("{", fp, "prg-open") :: printJson(q ++ 0, ode, fp) :: print("}", fp, "prg-close") :: Nil
    case AtomicODE(xp, e) => printJson(q ++ 0, xp, fp) :: op(expr, fp) :: printJson(q ++ 1, e, fp) :: Nil
    case t: DifferentialProduct => printJson(q ++ 0, t.left, fp) :: op(t, fp) :: printJson(q ++ 1, t.right, fp) :: Nil
    case c: DifferentialProgramConst => print(exprPrinter(c), fp) :: Nil
    case c: ProgramConst =>
      print(c.asString /* needs to be consistent with OpSpec.statementSemicolon (inaccessible here) */ + ";", fp) :: Nil
    case c: SystemConst =>
      print(c.asString /* needs to be consistent with OpSpec.statementSemicolon (inaccessible here) */ + ";", fp) :: Nil
  }

  /** Only first node's sequent is printed. */
  def nodesJson(
      nodes: List[ProofTreeNode],
      marginLeft: Int,
      marginRight: Int,
      printAllSequents: Boolean = false,
  ): List[(String, JsValue)] = {
    if (nodes.isEmpty) Nil
    else nodeJson(nodes.head, withSequent = true, marginLeft, marginRight) +:
      nodes.tail.map(nodeJson(_, withSequent = printAllSequents, marginLeft, marginRight))
  }

  def nodeJson(node: ProofTreeNode, withSequent: Boolean, marginLeft: Int, marginRight: Int): (String, JsValue) = {
    val id = JsString(node.id.toString)
    val sequent =
      if (withSequent) node.goal match {
        case None => JsNull
        case Some(goal) => sequentJson(goal, marginLeft, marginRight)
      }
      else JsNull
    val childrenIds = JsArray(node.children.map(s => JsString(s.id.toString)): _*)
    val parent = node.parent.map(n => JsString(n.id.toString)).getOrElse(JsNull)

    val posLocator =
      if (node.maker.isEmpty || node.maker.get.isEmpty) None
      else Try(BelleParser(node.maker.get)).toOption match { // @todo probably performance bottleneck
        case Some(pt: AppliedPositionTactic) => Some(pt.locator)
        case Some(pt: AppliedDependentPositionTactic) => Some(pt.locator)
        case _ => None
      }

    (
      node.id.toString,
      JsObject(
        "id" -> id,
        "isClosed" -> JsBoolean(node.numSubgoals <= 0),
        "sequent" -> sequent,
        "children" -> childrenIds,
        "rule" -> ruleJson(node.makerShortName.getOrElse(""), posLocator),
        "labels" -> JsArray(node.label.map(_.components).getOrElse(Nil).map(c => JsString(c.label)).toVector),
        "parent" -> parent,
      ),
    )
  }

  def sectionJson(section: List[String]): JsValue = { JsObject("path" -> JsArray(section.map(JsString(_)): _*)) }

  def deductionJson(deduction: List[List[String]]): JsValue =
    JsObject("sections" -> JsArray(deduction.map(sectionJson): _*))

  def itemJson(item: AgendaItem): (String, JsValue) = {
    val value = JsObject(
      "id" -> JsString(item.id),
      "name" -> JsString(item.name),
      "proofId" -> JsString(item.proofId),
      "deduction" -> deductionJson(List(item.path)),
    )
    (item.id, value)
  }

  def nodeIdJson(n: List[Int]): JsValue = JsNull
  def proofIdJson(n: String): JsValue = JsString(n)

  def ruleJson(ruleName: String, pos: Option[PositionLocator]): JsValue = {
    val belleTerm = ruleName.split("\\(")(0)
    val (name, codeName, asciiName, longName, maker, derivation: JsValue) =
      Try(DerivationInfo.ofCodeName(belleTerm)).toOption match {
        case Some(di) => (
            di.display.name,
            di.codeName,
            di.display.nameAscii,
            di.display.nameLong,
            ruleName,
            ApplicableAxiomsResponse(Nil, Map.empty, topLevel = true, pos)
              .derivationJson(di)
              .fields
              .getOrElse("derivation", JsNull),
          )
        case None => (ruleName, ruleName, ruleName, ruleName, ruleName, JsNull)
      }

    JsObject(
      "id" -> JsString(name),
      "name" -> JsString(name),
      "codeName" -> JsString(codeName),
      "asciiName" -> JsString(asciiName),
      "longName" -> JsString(longName),
      "maker" -> JsString(maker), // @note should be equal to codeName
      "pos" ->
        (pos match {
          case Some(Fixed(p, _, _)) => JsString(p.prettyString)
          case _ => JsString("")
        }),
      "derivation" -> derivation,
    )
  }

  def agendaItemJson(item: AgendaItemPOJO): JsValue = {
    JsObject(
      "agendaItemId" -> JsString(item.initialProofNode.toString),
      "proofId" -> JsString(item.proofId.toString),
      "displayName" -> JsString(item.displayName),
    )
  }
}
