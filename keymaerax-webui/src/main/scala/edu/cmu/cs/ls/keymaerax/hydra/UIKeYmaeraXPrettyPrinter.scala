/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXWeightedPrettyPrinter
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.parser.OpSpec.op
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._

object UIKeYmaeraXPrettyPrinter {
  private val HTML_OPEN = "$#@@$"
  private val HTML_CLOSE = "$@@#$"
  private val HTML_END_SPAN = s"$HTML_OPEN/span$HTML_CLOSE"

  //@todo custom OpSpec?
  private val rewritings = List(
    "&" -> "&#8743;",
    "!=" -> "&ne;",
    "!" -> "&not;",
    "|" -> "&#8744;",
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

  //private val opPattern: Regex = "(&|!=|!|\\||<->|->|<=|>=|\\\\forall|\\\\exists|\\[|\\]|<|>|\\$#@@\\$|\\$@@#\\$)".r

  /** UIKeYmaeraXPrettyPrinter(topId) is a UI pretty printer for sequent-formula with identifier topId */
  def apply(topId: String, plainText: Boolean): Expression=>String = new UIKeYmaeraXPrettyPrinter(topId, plainText)
}

/**
  * User-interface pretty printer for KeYmaera X syntax.
  * @author Andre Platzer
  */
class UIKeYmaeraXPrettyPrinter(val topId: String, val plainText: Boolean) extends KeYmaeraXWeightedPrettyPrinter {
  import UIKeYmaeraXPrettyPrinter._
  private def htmlSpan(c: String, body: String): String = s"""${HTML_OPEN}span class="$c"$HTML_CLOSE$body$HTML_END_SPAN"""

  private var topExpr: Expression = _
  //@note just to get isAnte right for UIIndex
  private val pos: Position = if (topId.startsWith("-")) AntePosition(1) else SuccPosition(1)

  override def apply(expr: Expression): String = {
    topExpr=expr
    rewritings.foldLeft(stringify(expr))({ case (s, (key, repl)) => s.replaceAllLiterally(key, repl) })
    //@note single pass with regex matching is slower than multi-pass literal replacement
    //val mapper = (m: Match) => rewritings.get(m.group(1))
    //opPattern.replaceSomeIn(stringify(expr), mapper)
  }

  protected override def emit(q: PosInExpr, s: String): String = {
    val hasStep = plainText || (topExpr match {
      case t: Term => UIIndex.allStepsAt(t.sub(q).get, Some(pos++q), None).isEmpty
      case f: Formula => UIIndex.allStepsAt(f.sub(q).get, Some(pos++q), None).isEmpty
    })

    val editable = !plainText && (topExpr match {
      case _: Term => false
      case f: Formula => f.sub(q).get match {
        case fml: Formula => fml.isFOL
        case _: Variable => false
        case _: Number => false
        case _: Term => true
        case _ => false
      }
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
    case _: Program => htmlSpan("k4-op k4-prg-op", super.ppOp(expr))
    case _ => super.ppOp(expr)
  }

  protected override def ppEnclosingOp(expr: Expression): (String, String) = expr match {
    case _: Box | _: Diamond =>
      htmlSpan("k4-mod-open", super.ppEnclosingOp(expr)._1) -> htmlSpan("k4-mod-close", super.ppEnclosingOp(expr)._2)
    case _: ODESystem | _: Program | _: DifferentialProgram | _: UnaryCompositeProgram =>
      htmlSpan("k4-prg-open", super.ppEnclosingOp(expr)._1) -> htmlSpan("k4-prg-close", super.ppEnclosingOp(expr)._2)
    case _ => super.ppEnclosingOp(expr)
  }

  protected override def pp(q: PosInExpr, term: Term): String = emit(q, term match {
    case t: Power =>
      wrapLeft(t, pp(q++0, t.left)) + "$#@@$sup$@@#$" + wrapRight(t, pp(q++1, t.right)) + "$#@@$/sup$@@#$"
    case _ => super.pp(q, term)
  })

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
        |  popover-is-open="tacticPopover.isOpen('$id')"
        |  popover-trigger="'none'"
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
