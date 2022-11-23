/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{FullPrettyPrinter, KeYmaeraXPrettierPrinter, KeYmaeraXWeightedPrettyPrinter}
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.parser.OpSpec.op
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, PosInExpr, Position, SuccPosition}
import org.typelevel.paiges.Doc

/** Prints HTML tags and HTML operators. */
trait HTMLPrinter {
  val HTML_OPEN: String = "$#@@$"
  val HTML_CLOSE: String = "$@@#$"
  val HTML_END_SPAN: String = htmlEndTag("span")

  //@todo custom OpSpec?
  val rewritings = List(
    "&" -> "&and;",
    "!=" -> "&ne;",
    "!" -> "&not;",
    "|" -> "&or;",
    "(&or;" -> "(|", // undo opening banana rewrite
    "&or;)" -> "|)", // undo closing banana rewrite
    "{&or;" -> "{|", // undo opening mustache rewrite
    "&or;}" -> "|}", // undo closing mustache rewrite
    "<->" -> "&#8596;",
    "->" -> "&rarr;",
    "<=" -> "&leq;",
    ">=" -> "&geq;",
    "\\forall" -> "&forall;",
    "\\exists" -> "&exist;",
    "[" -> "&#91;",
    "]" -> "&#93;",
    "++" -> "&#8746;",
    "<" -> "&lt;",
    ">" -> "&gt;",
    HTML_OPEN -> "<",
    HTML_CLOSE -> ">"
  )

  val textTagRewritings = List(
    "&" -> "&amp;",
    "<" -> "&lt;",
    ">" -> "&gt;",
    HTML_OPEN -> "<",
    HTML_CLOSE -> ">"
  )


  /** Returns an opening tag with encoded <>. */
  def htmlOpenTag(tag: String, clazz: Option[String] = None): String = clazz match {
    case None => s"$HTML_OPEN$tag$HTML_CLOSE"
    case Some(c) => s"""$HTML_OPEN$tag class="$c"$HTML_CLOSE"""
  }

  /** Returns a closing tag with encoded <>. */
  def htmlEndTag(tag: String): String = s"$HTML_OPEN/$tag$HTML_CLOSE"

  /** Returns the `body` enclosed in an encoded HTML `tag`. */
  def htmlElement(tag: String, body: String, clazz: Option[String] = None): String = htmlOpenTag(tag, clazz) + body + htmlEndTag(tag)

  /** Replaces KeYmaeraX syntax with HTML characters (e.g., < becomes &lt;) and introduces opening/closing tags HTML syntax. */
  def htmlEncode(html: String): String = {
    rewritings.foldLeft(html)({ case (s, (key, repl)) => s.replaceAllLiterally(key, repl) })
    //@note single pass with regex matching is slower than multi-pass literal replacement
    //val mapper = (m: Match) => rewritings.get(m.group(1))
    //opPattern.replaceSomeIn(stringify(expr), mapper)
  }

  /** Encodes HTML tags <>& etc. that may occur in text. */
  def htmlTagEncode(text: String): String = {
    textTagRewritings.foldLeft(text)({ case (s, (key, repl)) => s.replaceAllLiterally(key, repl) })
  }
}

class UIAbbreviatingKeYmaeraXPrettyPrinter extends KeYmaeraXWeightedPrettyPrinter {
  protected override def pp(q: PosInExpr, term: Term): String = term match {
    case FuncOf(Function(n, i, _, _, Some(_)), Nothing)   => emit(q, n + i.map("_" + _).getOrElse("") + "()")
    case FuncOf(Function(n, i, _, _, Some(_)), arg: Pair) => emit(q, n + i.map("_" + _).getOrElse("") + pp(q++0, arg))
    case FuncOf(Function(n, i, _, _, Some(_)), arg)       => emit(q, n + i.map("_" + _).getOrElse("") + "(" + pp(q++0, arg) + ")")
    case FuncOf(f, Nothing) => emit(q, f.asString + "()")
    case _ => super.pp(q, term)
  }
}

class UIAbbreviatingKeYmaeraXPrettierPrinter(margin: Int) extends KeYmaeraXPrettierPrinter(margin) {
  override def apply(expr: Expression): String = stringify(expr) ensures(
    //@note functions and interpreted functions are printed without parentheses/interpretations and do not reparse
    r => expr.kind == FunctionKind
      || StaticSemantics.symbols(expr).exists({ case Function(_, _, _, _, i) => i.isDefined case _ => false })
      || reparse(expr, r) == expr,
    "Expect parse of print to be identity." +
      //@todo reconcile first and last line of contract message
      "\nExpression: " + FullPrettyPrinter.stringify(expr) + "\t@ " + expr.getClass.getSimpleName +
      "\nPrinted:    " + stringify(expr) +
      "\nReparsed:   " + stringify(reparse(expr, stringify(expr))) + "\t@ " + reparse(expr, stringify(expr)).getClass.getSimpleName +
      "\nExpression: " + FullPrettyPrinter.stringify(reparse(expr, stringify(expr))) + "\t@ " + reparse(expr, stringify(expr)).getClass.getSimpleName +
      "\nExpected:   " + FullPrettyPrinter.stringify(expr) + "\t@ " + expr.getClass.getSimpleName
  )

  override def docOf(term: Term): Doc = term match {
    case FuncOf(Function(n, i, _, _, Some(_)), Nothing) => Doc.text(n + i.map("_" + _).getOrElse("") + "()")
    case FuncOf(Function(n, i, _, _, Some(_)), c: Pair) => (Doc.text(n + i.map("_" + _).getOrElse("")) + Doc.lineBreak + docOf(c)).grouped
    case FuncOf(Function(n, i, _, _, Some(_)), c)       => (Doc.text(n + i.map("_" + _).getOrElse("")) + encloseText("(", Doc.lineBreak + docOf(c), ")").nested(2)).grouped
    case _ => super.docOf(term)
  }
}

object UIKeYmaeraXPrettyPrinter extends HTMLPrinter {
  /** UIKeYmaeraXPrettyPrinter(topId) is a UI pretty printer for sequent-formula with identifier topId */
  def apply(topId: String, plainText: Boolean): Expression=>String = new UIKeYmaeraXPrettyPrinter(topId, plainText)
}

/**
  * User-interface pretty printer for KeYmaera X syntax.
  * @author Andre Platzer
  */
class UIKeYmaeraXPrettyPrinter(val topId: String, val plainText: Boolean) extends UIAbbreviatingKeYmaeraXPrettyPrinter {
  import UIKeYmaeraXPrettyPrinter._
  private def htmlSpan(c: String, body: String): String = htmlElement("span", body, Some(c))

  private var topExpr: Expression = _
  //@note just to get isAnte right for UIIndex
  private val pos: Position = if (topId.startsWith("-")) AntePosition(1) else SuccPosition(1)

  override def apply(expr: Expression): String = {
    topExpr=expr
    htmlEncode(stringify(expr))
  }

  protected override def emit(q: PosInExpr, s: String): String = {
    val hasStep = plainText || (topExpr match {
      case t: Term => UIIndex.allStepsAt(t.sub(q).get, Some(pos++q), None, Nil).isEmpty
      case f: Formula => UIIndex.allStepsAt(f.sub(q).get, Some(pos++q), None, Nil).isEmpty
      case _ => false
    })

    val editable = !plainText && (topExpr match {
      case f: Formula => f.sub(q).get match {
        case fml: Formula => fml.isFOL
        case _: Variable => false
        case _: Number => false
        case _: Term => true
        case _ => false
      }
      case _ => false
    })

    //@note base pretty printer emits a quantifier and its variable with same ID -> avoid spans with same ID
    val isQuantifiedVar = topExpr match {
      case f: Formula => f.sub(q) match {
        case Some(quant: Quantified) => !s.startsWith(ppOp(quant))
        case _ => false
      }
      case _ => false
    }

    if (isQuantifiedVar) s
    else {
      // emit complicated span only for elements with actual rule
      //@note problematic for drag&drop
      wrap(topId + (if (q.pos.nonEmpty) "," + q.pos.mkString(",") else ""), s, hasStep, editable)
    }
  }

  protected override def ppOp(expr: Expression): String = expr match {
    case _: Term => htmlSpan("k4-op k4-term-op", super.ppOp(expr))
    case _: CompositeFormula => htmlSpan("k4-op k4-propfml-op", super.ppOp(expr))
    case _: ComparisonFormula => htmlSpan("k4-op k4-cmpfml-op", super.ppOp(expr))
    case _: Formula => htmlSpan("k4-op k4-fml-op", super.ppOp(expr))
    case _: Dual => htmlSpan("k4-op k4-prg-op", s"${HTML_OPEN}sup$HTML_CLOSE@$HTML_OPEN/sup$HTML_CLOSE")
    case _: Program => htmlSpan("k4-op k4-prg-op", super.ppOp(expr))
    case _ => super.ppOp(expr)
  }

  protected override def wrap(text: String, expr: Expression): String = expr match {
    case _: Box  =>
      htmlSpan("k4-mod-open", "[") + text + htmlSpan("k4-mod-close", "]")
    case _: Diamond =>
      htmlSpan("k4-mod-open", "<") + text + htmlSpan("k4-mod-close", ">")
    case _: ODESystem | _: Program | _: DifferentialProgram | _: UnaryCompositeProgram =>
      htmlSpan("k4-prg-open", "{") + text + htmlSpan("k4-prg-close", "}")
    case _ => super.wrap(text, expr)
  }

  protected override def pp(q: PosInExpr, term: Term): String = term match {
    case t: Power => emit(q, wrapLeft(t, pp(q++0, t.left)) + s"${HTML_OPEN}sup$HTML_CLOSE" +
      wrapRight(t, pp(q++1, t.right)) + s"$HTML_OPEN/sup$HTML_CLOSE")
    case _ => super.pp(q, term)
  }

  private def wrap(id: String, content: String, plain: Boolean, editable: Boolean): String =
    if (plain && editable)
      s"""${HTML_OPEN}span id="fml_$id" ng-class="{'hl':modeIsEdit(), 'edithover':isEditFormulaHighlighted('$id')}"
         |  ng-mouseover="highlightFormula($$event, '$id', 'edit')"
         |  ng-mouseleave="highlightFormula($$event, undefined, 'edit')"
         |  ng-click="editClick('$id', $$event)"
         |  uib-popover-template="'templates/editFormulaPopoverTemplate.html'"
         |  popover-is-open="editFormulaPopover.isOpen('$id')"
         |  popover-trigger="'none'"
         |  popover-append-to-body="true"
         |  popover-placement="auto bottom"
         |$HTML_CLOSE$content$HTML_OPEN/span$HTML_CLOSE""".stripMargin
    else if (plain && !editable)
      s"""${HTML_OPEN}span id="fml_$id"$HTML_CLOSE$content$HTML_OPEN/span$HTML_CLOSE""".stripMargin
    else s"""${HTML_OPEN}span ng-class="{'hl':modeIsProve(), 'hlhover':isProveFormulaHighlighted('$id')}" id="$id"
        |  ng-mouseover="highlightFormula($$event, '$id', 'prove')"
        |  ng-mouseleave="highlightFormula($$event, undefined, 'prove')"
        |  ng-click="formulaClick('$id', $$event)"
        |  ng-right-click="formulaRightClick('$id', $$event)"
        |  uib-popover-template="'templates/axiomPopoverTemplate.html'"
        |  popover-trigger="'outsideClick'"
        |  popover-append-to-body="true"
        |  popover-placement="auto bottom"$HTML_CLOSE$content$HTML_OPEN/span$HTML_CLOSE""".stripMargin

  //@note drop
  //   k4-droppable on-drop="dndSink('$id').formulaDrop(dragData)"

  //@note drag&drop tooltip
  //  on-drag-enter="dndSink('$id').formulaDragEnter(dragData)"
  //  on-drag-leave="dndSink('$id').formulaDragLeave(dragData)"
  //  uib-tooltip-template="'templates/formulaDndTooltipTemplate.html'"
  //  tooltip-placement="bottom"
  //  tooltip-trigger="none" tooltip-is-open="dndTooltip.isOpen('$id')"


  //@todo
  override def apply(seq: Sequent): String = ???



  // symmetric space depending on left/right/both having parentheses
  protected override def spaceLeft(t: BinaryComposite, leftPrint: String): String = (skipParensLeft(t), skipParensRight(t)) match {
    case (true, true) => leftPrint + (" " * balanceWeight(t))
    case (true, false) => leftPrint + (" " * weight(t.right, t))
    case (false, true) => leftPrint + (" " * weight(t.left, t))
    case (false, false) => leftPrint + " "
  }
  protected override def spaceRight(t: BinaryComposite, rightPrint: String): String = (skipParensLeft(t), skipParensRight(t)) match {
      case (true, true) => (" " * balanceWeight(t)) + rightPrint
      case (true, false) => (" " * weight(t.right, t)) + rightPrint
      case (false, true) => (" " * weight(t.left, t)) + rightPrint
      case (false, false) => " " + rightPrint
    }

  private def balanceWeight(par: BinaryComposite): Int = Math.max(weight(par.left, par), weight(par.right, par))

  protected override def weight(sub: Expression, par: BinaryComposite): Int = {
    val prec = op(par).prec
    val subPrec = op(sub).prec

    def prec2weight(prec: Int) =
      if (prec >= 200)
        // programs are formatted relative to one another not with their ridiculously large prec
        (prec-150) / 50
      else
        prec / 50

    // adapt own weight by sub operator weight
    (prec2weight(subPrec)/2) * prec2weight(prec)
  }

//  override val parser = new Parser() {
//    def apply(input: String): Expression = throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.parser is undefined since not parsing HTML")
//    val termParser: (String => Term) = s => throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.parser is undefined since not parsing HTML")
//    val formulaParser: (String => Formula) = s => throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.parser is undefined since not parsing HTML")
//    val programParser: (String => Program) = s => throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.parser is undefined since not parsing HTML")
//    val differentialProgramParser: (String => DifferentialProgram) = s => throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.parser is undefined since not parsing HTML")
//    val printer: PrettyPrinter = UIKeYmaeraXPrettyPrinter.this
//  }
  override val fullPrinter: (Expression => String) = (e:Expression) => throw new UnsupportedOperationException("UIKeYmaeraXPrettyPrinter.fullPrinter not implemented yet")
}

object UIKeYmaeraXAxiomPrettyPrinter {
  lazy val pp = new UIKeYmaeraXAxiomPrettyPrinter()
}

/**
  * User-interface pretty printer for UI axiom entries.
  * @author Stefan Mitsch
  */
class UIKeYmaeraXAxiomPrettyPrinter extends KeYmaeraXWeightedPrettyPrinter with HTMLPrinter {
  override def apply(expr: Expression): String = htmlEncode(stringify(expr))

  /** Print name, suffix _ stripped. */
  private def printName(s: NamedSymbol): String = s.index match {
    case None => s.name.stripSuffix("_")
    case Some(idx) => s.name.stripSuffix("_") + "_" + idx
  }

  private def printSpace(s: Space): String = s match {
    case AnyArg => "⦅⦆" //s"(${HTML_OPEN}b$HTML_CLOSE${HTML_OPEN}i$HTML_CLOSE" + "x" + s"$HTML_OPEN/i$HTML_CLOSE$HTML_OPEN/b$HTML_CLOSE)"
    case Except(vs) => s"(${HTML_OPEN}s$HTML_CLOSE" + vs.map(printName).mkString(",") + s"$HTML_OPEN/s$HTML_CLOSE)"
  }

  protected override def pp(q: PosInExpr, fml: Formula): String = emit(q, fml match {
    case PredOf(p, Nothing) => printName(p)
    case PredOf(p, arg) => printName(p) + "(" + pp(q++PosInExpr(0::Nil), arg) + ")"
    case p@UnitPredicational(_, AnyArg) => printName(p).toUpperCase
    case p@UnitPredicational(_, s) => printName(p) + printSpace(s)
    case _ => super.pp(q, fml)
  })

  protected override def pp(q: PosInExpr, term: Term): String = emit(q, term match {
    case FuncOf(f, Nothing) => printName(f)
    case FuncOf(f, arg) => printName(f) + "(" + pp(q++PosInExpr(0::Nil), arg) + ")"
    case v: BaseVariable => printName(v)
    case v: DifferentialSymbol => printName(v.x) + "'"
    case f@UnitFunctional(_, AnyArg, _) => printName(f).toUpperCase
    case f@UnitFunctional(_, s, _) => printName(f) + printSpace(s)
    case t: Power =>
      wrapLeft(t, pp(q++0, t.left)) + s"${HTML_OPEN}sup$HTML_CLOSE" + wrapRight(t, pp(q++1, t.right)) + s"$HTML_OPEN/sup$HTML_CLOSE"
    case _ => super.pp(q, term)
  })

  protected override def pp(q: PosInExpr, program: Program): String = emit(q, program match {
    case a: ProgramConst => printName(a) + ";"
    case a: SystemConst => printName(a) + ";"
    case a: NamedSymbol => printName(a)
    case _ => super.pp(q, program)
  })

  protected override def ppODE(q: PosInExpr, program: DifferentialProgram): String = emit(q, program match {
    case a@DifferentialProgramConst(_, s) => printName(a) + printSpace(s)
    case _ => super.ppODE(q, program)
  })

  override def apply(seq: Sequent): String = ???

  // symmetric space depending on left/right/both having parentheses
  protected override def spaceLeft(t: BinaryComposite, leftPrint: String): String = (skipParensLeft(t), skipParensRight(t)) match {
    case (true, true) => leftPrint + (" " * balanceWeight(t))
    case (true, false) => leftPrint + (" " * weight(t.right, t))
    case (false, true) => leftPrint + (" " * weight(t.left, t))
    case (false, false) => leftPrint + " "
  }
  protected override def spaceRight(t: BinaryComposite, rightPrint: String): String = (skipParensLeft(t), skipParensRight(t)) match {
    case (true, true) => (" " * balanceWeight(t)) + rightPrint
    case (true, false) => (" " * weight(t.right, t)) + rightPrint
    case (false, true) => (" " * weight(t.left, t)) + rightPrint
    case (false, false) => " " + rightPrint
  }

  private def balanceWeight(par: BinaryComposite): Int = Math.max(weight(par.left, par), weight(par.right, par))

  protected override def weight(sub: Expression, par: BinaryComposite): Int = {
    val prec = op(par).prec
    val subPrec = op(sub).prec

    def prec2weight(prec: Int) =
      if (prec >= 200)
      // programs are formatted relative to one another not with their ridiculously large prec
        (prec-150) / 50
      else
        prec / 50

    // adapt own weight by sub operator weight
    (prec2weight(subPrec)/2) * prec2weight(prec)
  }

  override val fullPrinter: (Expression => String) = (e:Expression) => throw new UnsupportedOperationException("UIKeYmaeraXAxiomPrettyPrinter.fullPrinter not implemented yet")
}
