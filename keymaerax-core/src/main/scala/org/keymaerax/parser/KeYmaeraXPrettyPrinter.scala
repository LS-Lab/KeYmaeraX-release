/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Differential Dynamic Logic pretty printer in concrete KeYmaera X notation.
 *
 * @author
 *   Andre Platzer
 * @see
 *   "Andre Platzer. A uniform substitution calculus for differential dynamic logic. arXiv 1503.01981, 2015."
 * @note
 *   Code Review 2016-08-02
 */
package org.keymaerax.parser

import org.keymaerax.GlobalState
import org.keymaerax.core._
import org.keymaerax.infrastruct.PosInExpr
import org.keymaerax.infrastruct.PosInExpr.HereP
import org.keymaerax.parser.OpSpec.op

import scala.annotation.tailrec
import scala.collection.immutable._
import scala.collection.mutable.ListBuffer

/**
 * Default KeYmaera X Pretty Printer formats differential dynamic logic expressions
 *
 * @see
 *   [[org.keymaerax.parser.KeYmaeraXPrecedencePrinter]]
 */
object KeYmaeraXPrettyPrinter extends KeYmaeraXPrecedencePrinter {

  /** This default pretty printer. */
  val pp: KeYmaeraXPrettyPrinter.type = this
}

/**
 * KeYmaera X Pretty Printer without contract checking
 *
 * @see
 *   [[org.keymaerax.parser.KeYmaeraXPrecedencePrinter]]
 */
object KeYmaeraXNoContractPrettyPrinter extends KeYmaeraXPrecedencePrinter {

  /** This default pretty printer without contract checking. */
  val pp: KeYmaeraXNoContractPrettyPrinter.type = this

  override def apply(expr: Expression): String = stringify(expr)
}

/** Common base functionality for KeYmaera X Pretty Printers. */
trait BasePrettyPrinter extends PrettyPrinter {

  /** Pretty-print term to a string */
  def apply(expr: Expression): String = stringify(expr) ensures
    (
      r => expr.kind == FunctionKind || reparse(expr, r) == expr,
      "Expect parse of print to be identity." +
        // @todo reconcile first and last line of contract message
        "\nExpression: " + FullPrettyPrinter.stringify(expr) + "\t@ " + expr.getClass.getSimpleName + "\nPrinted:    " +
        stringify(expr) + "\nReparsed:   " + stringify(reparse(expr, stringify(expr))) + "\t@ " +
        reparse(expr, stringify(expr)).getClass.getSimpleName + "\nExpression: " +
        FullPrettyPrinter.stringify(reparse(expr, stringify(expr))) + "\t@ " +
        reparse(expr, stringify(expr)).getClass.getSimpleName + "\nExpected:   " + FullPrettyPrinter.stringify(expr) +
        "\t@ " + expr.getClass.getSimpleName,
    )

  /** Pretty-print sequent to a string */
  def apply(seq: Sequent): String = {
    val anteLines = seq
      .ante
      .zipWithIndex
      .map { case (formula, i) => s"${-(i + 1)}:  ${apply(formula)}\t${formula.getClass.getSimpleName}" }
    val succLines = seq
      .succ
      .zipWithIndex
      .map { case (formula, i) => s"${i + 1}:  ${apply(formula)}\t${formula.getClass.getSimpleName}" }

    anteLines.concat(" ==>  " :: Nil).concat(succLines).mkString("\n")
  }

  /** Pretty-print sequent to a string but without contract checking! */
  private[keymaerax] def stringify(seq: Sequent): String = {
    val anteLines = seq
      .ante
      .zipWithIndex
      .map { case (formula, i) => s"${-(i + 1)}:  ${stringify(formula)}\t${formula.getClass.getSimpleName}" }
    val succLines = seq
      .succ
      .zipWithIndex
      .map { case (formula, i) => s"${i + 1}:  ${stringify(formula)}\t${formula.getClass.getSimpleName}" }

    anteLines.concat(" ==>  " :: Nil).concat(succLines).mkString("\n")
  }

  /** Reparse the string print as the same kind as expr has */
  protected[keymaerax] def reparse(expr: Expression, print: String): Expression = expr.kind match {
    case TermKind => parser.termParser(print)
    case FormulaKind => parser.formulaParser(print)
    case ProgramKind => parser.programParser(print)
    case DifferentialProgramKind => parser.differentialProgramParser(print)
    case FunctionKind => throw new AssertionError("No completed expressions of FunctionKind can be constructed")
    case ExpressionKind => throw new AssertionError("No expressions of ExpressionKind can be constructed")
  }

  /** Pretty-print term to a string but without contract checking! */
  private[keymaerax] def stringify(expr: Expression): String
}

/**
 * Fully-parenthesized pretty printer in full form with full parentheses.
 *
 * @example
 *   Fully parenthesized strings are obtained using the [[org.keymaerax.parser.FullPrettyPrinter]] printer:
 *   {{{
 *   val pp = FullPrettyPrinter
 *   // "x < -(y)"
 *   val fml0 = Less(Variable("x"),Neg(Variable("y")))
 *   val fml0str = pp(fml0)
 *   // "true -> ([x:=1;](x>=0))"
 *   val fml1 = Imply(True, Box(Assign(Variable("x"), Number(1)), GreaterEqual(Variable("x"), Number(0))))
 *   val fml1str = pp(fml1)
 *   }}}
 * @author
 *   Andre Platzer
 * @see
 *   [[org.keymaerax.parser.KeYmaeraXPrinter.fullPrinter]]
 */
object FullPrettyPrinter extends BasePrettyPrinter {

  import OpSpec.{op, statementSemicolon}

  val parser: Parser = GlobalState.parser
  val fullPrinter: (Expression => String) = this

  /** Pretty-print term to a string but without contract checking! */
  private[keymaerax] def stringify(expr: Expression): String = expr match {
    case t: Term => pp(t)
    case f: Formula => pp(f)
    case p: Program => pp(p)
    case f: Function => f.asString
  }

  /**
   * @note
   *   The extra space disambiguates x<-7 as in x < (-7) from x REVIMPLY 7 as well as x<-(x^2) from x REVIMPLY ...
   */
  private val LEXSPACE: String = " "

  private def pp(term: Term): String = term match {
    case Nothing => op(term).opcode
    // @note DotTerm does not have an OpSpec img because it has concrete names (similar to variables)
    case DotTerm(sort, idx) => "." +
        (idx match {
          case None => ""
          case Some(i) => "_" + i
        }) +
        (sort match {
          case Tuple(_, _) => sort.toString
          case _ => ""
        }) // @note will parse as Pair(Variable("Real"), ...), which has Sort sort
    case DifferentialSymbol(x) => pp(x) + op(term).opcode
    case x: Variable => x.asString
    case Differential(t) => "(" + pp(t) + ")" + op(term).opcode
    // @note forcing parentheses around numbers to avoid Neg(Times(Number(5),Variable("x")) to be printed as -5*x yet reparsed as (-5)*x. Alternatively could add space after unary Neg.
    case Number(n) => "(" + n.bigDecimal.toPlainString + ")"
    case FuncOf(f, c) => f.asString + "(" + pp(c) + ")"
    // special notation
    case Pair(l, r) => "(" + pp(l) + op(term).opcode + pp(r) + ")"
    case UnitFunctional(name, space, sort) => name + "(" + space + ")"
    // @note all remaining unary operators are prefix, see [[OpSpec]]
    case t: UnaryCompositeTerm => op(t).opcode + "(" + pp(t.child) + ")"
    // @note all binary operators are infix, see [[OpSpec]]
    case t: BinaryCompositeTerm => "(" + pp(t.left) + ")" + op(t).opcode + "(" + pp(t.right) + ")"
  }

  private def pp(formula: Formula): String = formula match {
    case True | False | DotFormula => op(formula).opcode
    case PredOf(p, c) => p.asString + "(" + pp(c) + ")"
    case PredicationalOf(p, c) => p.asString + "{" + pp(c) + "}"
    case f: ComparisonFormula => "(" + pp(f.left) + ")" + LEXSPACE + op(formula).opcode + LEXSPACE + "(" + pp(f.right) +
        ")"
    case DifferentialFormula(g) => "(" + pp(g) + ")" + op(formula).opcode
    case f: Quantified => op(formula).opcode + " " + f.vars.map(pp).mkString(",") + " " + "(" + pp(f.child) + ")"
    case f: Box => "[" + pp(f.program) + "]" + "(" + pp(f.child) + ")"
    case f: Diamond => "<" + pp(f.program) + ">" + "(" + pp(f.child) + ")"
    case UnitPredicational(name, space) =>
      if (name == ReservedSymbols.exerciseP.name) "__________" else name + "(" + space + ")"
    // @note all remaining unary operators are prefix, see [[OpSpec]]
    case t: UnaryCompositeFormula => op(t).opcode + "(" + pp(t.child) + ")"
    // @note all binary operators are infix, see [[OpSpec]]
    case t: BinaryCompositeFormula => "(" + pp(t.left) + ")" + op(t).opcode + "(" + pp(t.right) + ")"
  }

  private def pp(program: Program): String = program match {
    case a: ProgramConst => statement(a.asString)
    case a: SystemConst =>
      if (a.name == ReservedSymbols.exerciseS.name) statement("__________") else statement(a.toString)
    case Assign(x, e) => statement(pp(x) + op(program).opcode + pp(e))
    case AssignAny(x) => statement(pp(x) + op(program).opcode)
    case Test(f) => statement(op(program).opcode + "(" + pp(f) + ")")
    case ODESystem(ode, True) => "{" + ppODE(ode) + "}"
    case ODESystem(ode, f) => "{" + ppODE(ode) + op(program).opcode + pp(f) + "}"
    // @note unambiguously reparse as ODE not as equation that happens to involve a differential symbol.
    // @note This is only used in printing internal data structures, not user input.
    case ode: DifferentialProgram => "{" + ppODE(ode) + "}"
    // @note all remaining unary operators are prefix, see [[OpSpec]]
    case t: UnaryCompositeProgram => "{" + pp(t.child) + "}" + op(program).opcode
//    case t: Compose if OpSpec.statementSemicolon =>
//      //@note in statementSemicolon mode, suppress opcode of Compose since already after each statement
//      "{" + pp(t.left) + "}" + /*op(t).opcode + */ "{" + pp(t.right) + "}"
    // @note all binary operators are infix, see [[OpSpec]]
    case t: BinaryCompositeProgram => "{" + pp(t.left) + "}" + op(t).opcode + "{" + pp(t.right) + "}"
  }

  private def ppODE(program: DifferentialProgram): String = program match {
    case a: DifferentialProgramConst => if (a.name == ReservedSymbols.exerciseD.name) "__________" else a.asString
    case AtomicODE(xp, e) => pp(xp) + op(program).opcode + pp(e)
    case t: DifferentialProduct =>
      assert(
        op(t).assoc == RightAssociative && !t.left.isInstanceOf[DifferentialProduct],
        "differential products are always right-associative",
      )
      ppODE(t.left) + op(t).opcode + ppODE(t.right)
  }

  /** Formatting the atomic statement s */
  protected def statement(s: String): String = if (statementSemicolon) s + ";" else s

}

/**
 * Vanilla: KeYmaera X Printer formats differential dynamic logic expressions in KeYmaera X notation according to the
 * concrete syntax of differential dynamic logic with explicit statement end ``;`` operator.
 *
 * @example
 *   Printing formulas to strings is straightforward using [[org.keymaerax.parser.KeYmaeraXPrettyPrinter.apply]]:
 *   {{{
 *   val pp = KeYmaeraXPrettyPrinter
 *   // "x < -y"
 *   val fml0 = Less(Variable("x"),Neg(Variable("y")))
 *   val fml0str = pp(fml0)
 *   // "true -> [x:=1;]x>=0"
 *   val fml1 = Imply(True, Box(Assign(Variable("x"), Number(1)), GreaterEqual(Variable("x"), Number(0))))
 *   val fml1str = pp(fml1)
 *   }}}
 * @author
 *   Andre Platzer
 * @see
 *   [[org.keymaerax.parser]]
 * @see
 *   [[http://keymaeraX.org/doc/dL-grammar.md Grammar]]
 * @see
 *   [[https://github.com/LS-Lab/KeYmaeraX-release/wiki/KeYmaera-X-Syntax-and-Informal-Semantics Wiki]]
 */
class KeYmaeraXPrinter extends BasePrettyPrinter {

  import OpSpec.{op, statementSemicolon}

  lazy val parser: Parser = GlobalState.parser
  val fullPrinter: (Expression => String) = FullPrettyPrinter

  /** Pretty-print term to a string but without contract checking! */
  private[keymaerax] def stringify(expr: Expression) = expr match {
    case t: Term => pp(HereP, t)
    case f: Formula => pp(HereP, f)
    case p: Program => pp(HereP, p)
    case f: Function => f.asString
  }

  /** True if negative numbers should get extra parentheses */
  private[parser] val negativeBrackets = !OpSpec.negativeNumber

  /**
   * @note
   *   The extra space disambiguates `x<-7` as in `x < (-7)` from `x REVIMPLY 7` as well as `x<-(x^2)` from `x REVIMPLY
   *   ...`
   */
  private val LEXSPACE: String = " "

  /** Pretty-print the operator of a term */
  protected def ppOp(expr: Expression): String = expr match {
    // @note in statementSemicolon mode, suppress opcode of Compose since already after each statement
    case _: Compose if OpSpec.statementSemicolon => ""
    case _ => op(expr).opcode
  }

  /** Pretty-print enclosing parentheses, braces, brackets etc. */
  protected def wrap(text: String, expr: Expression): String = expr match {
    case _: Box => "[" + text + "]"
    case _: Diamond => "<" + text + ">"
    case _: Program => "{" + text + "}"
    case _: PredOf => "(" + text + ")"
    case _: Pair => "(" + text + ")"
    case _: PredicationalOf => "{" + text + "}"
    case _ => throw new AssertionError("no parenthetical expression " + expr)
  }

  // @todo could add contract that TermAugmentor(original)(q) == term
  protected def pp(q: PosInExpr, term: Term): String = emit(
    q,
    term match {
      case Nothing => ppOp(term)
      case DotTerm(sort, idx) => "." +
          (idx match {
            case None => ""
            case Some(i) => "_" + i
          }) +
          (sort match {
            case Tuple(_, _) => sort.toString
            case _ => ""
          }) // @note will parse as Pair(Variable("Real"), ...), which has Sort sort
      case DifferentialSymbol(x) => x.asString + ppOp(term)
      case x: Variable => x.asString
      // disambiguate (-2)' versus (-(2))' versus ((-2))'
      // @note duplicates Differential(Number) to avoid accidental side-effect of changing Differential/Number when overriding pp
      case Differential(Number(n)) if negativeBrackets =>
        if (n < 0) "((" + n.bigDecimal.toPlainString + "))" + ppOp(term)
        else "(" + n.bigDecimal.toPlainString + ")" + ppOp(term)
      case Differential(t) => "(" + pp(q ++ 0, t) + ")" + ppOp(term)
      // special case forcing parentheses around numbers to avoid Neg(Times(Number(5),Variable("x")) to be printed as -5*x yet reparsed as (-5)*x. Alternatively could add space after unary Neg.
      case Number(n) =>
        if (negativeBrackets) { if (n < 0) "(" + n.bigDecimal.toPlainString + ")" else n.bigDecimal.toPlainString }
        else n.bigDecimal.toPlainString
      case FuncOf(f, c) =>
        if (f.domain.isInstanceOf[Tuple]) f.asString + pp(q ++ 0, c) else f.asString + "(" + pp(q ++ 0, c) + ")"
      // special notation
      case p: Pair =>
        // @todo create positions when flattening pairs
        /** Flattens pairs in right-associative way */
        def flattenPairs(e: Term): List[Term] = e match {
          case Pair(l, r) => l :: flattenPairs(r)
          case t => t :: Nil
        }
        val flattened = flattenPairs(p)
        // PosInExpr for a list [a,b,c,d] ~> .0, .1.0, .1.1.0, .1.1.1, which are the binary digits of [0,2,6,7] computed as [2^1-2, 2^2-2, 2^3-2, 2^3-1]
        val posInExprs = ListBuffer.empty[PosInExpr]
        for (i <- flattened.indices.takeRight(flattened.size - 1)) {
          // (1<<i)-2 go right i-2 times, then go left
          posInExprs.append(PosInExpr(((1 << i) - 2).toBinaryString.map(_.asDigit).toList))
        }
        posInExprs.append(PosInExpr(((1 << posInExprs.size) - 1).toBinaryString.map(_.asDigit).toList))
        wrap(flattened.zipWithIndex.map({ case (p, i) => pp(q ++ posInExprs(i), p) }).mkString(ppOp(term)), term)
      case UnitFunctional(name, space, sort) =>
        if (name == ReservedSymbols.exerciseF.name) "__________" else name + "(" + space + ")"
      // special case when negative numbers are enabled: force to disambiguate between -5 as in the number (-5) as opposed to -(5).
      case t @ Neg(n: Number) if !negativeBrackets => ppOp(t) + "(" + pp(q ++ 0, n) + ")"
      // special case forcing space between unary negation and numbers to avoid Neg(Times(Number(5),Variable("x")) to be printed as -5*x yet reparsed as (-5)*x.
      case t @ Neg(n: Number) if !negativeBrackets => ppOp(t) + " " + wrapChild(t, pp(q ++ 0, n))
      case t @ Neg(x) if !OpSpec.weakNeg => ppOp(t) + "(" + pp(q ++ 0, x) + ")"
      // @note all remaining unary operators are prefix, see [[OpSpec]]
      case t: UnaryCompositeTerm => ppOp(t) + wrapChild(t, pp(q ++ 0, t.child))
      // @note all binary operators are infix, see [[OpSpec]]
      case t: BinaryCompositeTerm =>
        // special case forcing space between unary negation and numbers when negative brackets are enabled to disambiguate (- 1)^2 from (-1)^2
        def printSub(i: Int, t: Term): String = t match {
          case Neg(n: Number) if negativeBrackets => ppOp(t) + " " + pp(q ++ i, n)
          case _ => pp(q ++ i, t)
        }
        wrapLeft(t, printSub(0, t.left)) + ppOp(t) + wrapRight(t, printSub(1, t.right))
    },
  )

  protected def pp(q: PosInExpr, formula: Formula): String = emit(
    q,
    formula match {
      case True | False | DotFormula => ppOp(formula)
      case PredOf(p, c) =>
        if (p.domain.isInstanceOf[Tuple]) p.asString + pp(q ++ 0, c) else p.asString + "(" + pp(q ++ 0, c) + ")"
      case PredicationalOf(p, c) => p.asString + "{" + pp(q ++ 0, c) + "}"
      // special case to disambiguate between x<-y as in x < -y compared to x REVIMPLY y
      case f: Less => wrapLeft(f, pp(q ++ 0, f.left)) + LEXSPACE + ppOp(formula) + LEXSPACE +
          wrapRight(f, pp(q ++ 1, f.right))
      case f: ComparisonFormula => wrapLeft(f, pp(q ++ 0, f.left)) + ppOp(formula) + wrapRight(f, pp(q ++ 1, f.right))
      case DifferentialFormula(g) => "(" + pp(q ++ 0, g) + ")" + ppOp(formula)
      // @note the q position for variables is a little weird since it identifies the quantifier not the variable
      case f: Quantified => ppOp(formula) + " " + f.vars.map(pp(q, _)).mkString(",") + " " +
          wrapChild(f, pp(q ++ 0, f.child))
      case f: Box => wrap(pp(q ++ 0, f.program), f) + wrapChild(f, pp(q ++ 1, f.child))
      case f: Diamond => wrap(pp(q ++ 0, f.program), f) + wrapChild(f, pp(q ++ 1, f.child))
      case UnitPredicational(name, space) => name + "(" + space + ")"
      // @note all remaining unary operators are prefix, see [[OpSpec]]
      case t: UnaryCompositeFormula => ppOp(t) + wrapChild(t, pp(q ++ 0, t.child))
      // @note all binary operators are infix, see [[OpSpec]]
      case t: BinaryCompositeFormula => wrapLeft(t, pp(q ++ 0, t.left)) + ppOp(t) + wrapRight(t, pp(q ++ 1, t.right))
    },
  )

  protected def pp(q: PosInExpr, program: Program): String = emit(
    q,
    program match {
      case a: ProgramConst => statement(a.asString)
      case a: SystemConst => statement(a.toString)
      case Assign(x, e) => statement(pp(q ++ 0, x) + ppOp(program) + pp(q ++ 1, e))
      case AssignAny(x) => statement(pp(q ++ 0, x) + ppOp(program))
      case Test(f) => statement(ppOp(program) + pp(q ++ 0, f))
      case ODESystem(ode, True) => wrap(ppODE(q ++ 0, ode), program)
      case ODESystem(ode, f) => wrap(ppODE(q ++ 0, ode) + ppOp(program) + pp(q ++ 1, f), program)
      // @note unambiguously reparse as ODE not as equation that happens to involve a differential symbol.
      // @note This is only used in printing internal data structures, not user input (ODESystem case catches user input).
      // @note no positional change since ODESystem already descended into child position
      case ode: DifferentialProgram => wrap(ppODE(q, ode), program)
      // @note forced parentheses in grammar for loops and duals
      case t: UnaryCompositeProgram => wrap(pp(q ++ 0, t.child), program) + ppOp(program)
      case t: Compose => pwrapLeft(t, pp(q ++ 0, t.left)) + ppOp(t) + pwrapRight(t, pp(q ++ 1, t.right))
      case t: BinaryCompositeProgram => pwrapLeft(t, pp(q ++ 0, t.left)) + ppOp(t) + pwrapRight(t, pp(q ++ 1, t.right))
    },
  )

  protected def ppODE(q: PosInExpr, program: DifferentialProgram): String = emit(
    q,
    program match {
      case a: DifferentialProgramConst => a.asString
      case AtomicODE(xp, e) => pp(q ++ 0, xp) + ppOp(program) + pp(q ++ 1, e)
      case t: DifferentialProduct =>
        assert(
          op(t).assoc == RightAssociative && !t.left.isInstanceOf[DifferentialProduct],
          "differential products are always right-associative",
        )
        ppODE(q ++ 0, t.left) + ppOp(t) + ppODE(q ++ 1, t.right)
    },
  )

  // parentheses wrapping and emission

  /** Wrap `childPrint` for `t.child` in parentheses if they are not implicit. */
  protected def wrapChild(t: UnaryComposite, childPrint: String): String = "(" + childPrint + ")"

  /** Wrap `childPrint` for `t.child` in parentheses if they are not implicit. */
  protected def wrapChild(t: Quantified, childPrint: String): String = "(" + childPrint + ")"

  /** Wrap `childPrint` for `t.child` in parentheses if they are not implicit. */
  protected def wrapChild(t: Modal, childPrint: String): String = "(" + childPrint + ")"

  /** Wrap `leftPrint` for `t.left` in parentheses if they are not implicit. */
  protected def wrapLeft(t: BinaryComposite, leftPrint: String): String = "(" + leftPrint + ")"

  /** Wrap `rightPrint` for `t.right` in parentheses if they are not implicit. */
  protected def wrapRight(t: BinaryComposite, rightPrint: String): String = "(" + rightPrint + ")"

  /** Wrap `leftPrint` for `t.left` in program parentheses if they are not implicit. */
  protected def pwrapLeft(t: BinaryComposite /*Differential/Program*/, leftPrint: String): String = "{" + leftPrint +
    "}"

  /** Wrap `rightPrint` for `t.right` in program parentheses if they are not implicit. */
  protected def pwrapRight(t: BinaryComposite /*Differential/Program*/, rightPrint: String): String = "{" + rightPrint +
    "}"

  /** Emit the string `s` as a result of the pretty-printer for the expression at position `q` */
  protected def emit(q: PosInExpr, s: String): String = s

  /** Formatting the atomic statement s */
  protected def statement(s: String): String = if (statementSemicolon) s + ";" else s

}

// additional pretty printers

/** Fully parenthesized pretty printer that is functionally equivalent to [[FullPrettyPrinter]] */
object FullPrettyPrinter0 extends KeYmaeraXPrinter {
  // @note no contract to avoid recursive checking of contracts in error messages of KeYmaeraXPrinter.apply
  override def apply(expr: Expression): String = stringify(expr)
}

/**
 * KeYmaera X Printer base class formatting based on parentheses skipping decisions.
 *
 * @author
 *   Andre Platzer
 */
abstract class KeYmaeraXSkipPrinter extends KeYmaeraXPrinter {
  protected override def wrapChild(t: UnaryComposite, childPrint: String): String =
    if (skipParens(t)) childPrint else "(" + childPrint + ")"
  protected override def wrapChild(t: Quantified, childPrint: String): String =
    if (skipParens(t)) childPrint else "(" + childPrint + ")"
  protected override def wrapChild(t: Modal, childPrint: String): String =
    if (skipParens(t)) childPrint else "(" + childPrint + ")"

  protected override def wrapLeft(t: BinaryComposite, leftPrint: String): String =
    if (skipParensLeft(t)) leftPrint else "(" + leftPrint + ")"
  protected override def wrapRight(t: BinaryComposite, rightPrint: String): String =
    if (skipParensRight(t)) rightPrint else "(" + rightPrint + ")"

  protected override def pwrapLeft(t: BinaryComposite /*Differential/Program*/, leftPrint: String): String =
    if (skipParensLeft(t)) leftPrint else "{" + leftPrint + "}"
  protected override def pwrapRight(t: BinaryComposite /*Differential/Program*/, rightPrint: String): String =
    if (skipParensRight(t)) rightPrint else "{" + rightPrint + "}"

  /**
   * Whether parentheses around `t.child` can be skipped because they are implicit.
   * @see
   *   [[wrapChild()]]
   */
  protected def skipParens(t: UnaryComposite): Boolean

  /**
   * Whether parentheses around `t.child` can be skipped because they are implicit.
   * @see
   *   [[wrapChild()]]
   */
  protected def skipParens(t: Quantified): Boolean

  /**
   * Whether parentheses around `t.child` can be skipped because they are implicit.
   * @see
   *   [[wrapChild()]]
   */
  protected def skipParens(t: Modal): Boolean

  /**
   * Whether parentheses around `t.left` can be skipped because they are implicit.
   * @note
   *   Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
   * @see
   *   [[wrapLeft()]]
   */
  protected def skipParensLeft(t: BinaryComposite): Boolean

  /**
   * Whether parentheses around `t.right` can be skipped because they are implicit.
   * @note
   *   Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
   * @see
   *   [[wrapRight()]]
   */
  protected def skipParensRight(t: BinaryComposite): Boolean

}

/**
 * Precedence-based: KeYmaera X Pretty Printer formats differential dynamic logic expressions with compact brackets in
 * KeYmaera X notation according to the concrete syntax of differential dynamic logic with explicit statement end `;`
 * operator.
 * @author
 *   Andre Platzer
 * @todo
 *   Augment with ensures postconditions that check correct reparse non-recursively.
 * @see
 *   [[http://keymaeraX.org/doc/dL-grammar.md Grammar]]
 */
class KeYmaeraXPrecedencePrinter extends KeYmaeraXSkipPrinter {

  /** @inheritdoc */
  protected override def skipParens(t: UnaryComposite): Boolean =
    if (OpSpec.negativeNumber && t.isInstanceOf[Term]) op(t.child) <= op(t) && !leftMostLeaf(t.child)
      .exists(_.isInstanceOf[Number])
    else op(t.child) <= op(t)

  @tailrec
  private def leftMostLeaf(t: Expression): Option[Expression] = t match {
    case _: UnaryComposite => None
    case b: BinaryComposite => leftMostLeaf(b.left)
    case x => Some(x)
  }

  /** @inheritdoc */
  protected override def skipParens(t: Quantified): Boolean = op(t.child) <= op(t)

  /** @inheritdoc */
  protected override def skipParens(t: Modal): Boolean = op(t.child) <= op(t)

  /**
   * Whether parentheses around `t.left` can be skipped because they are implied.
   * @note
   *   Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
   */
  protected override def skipParensLeft(t: BinaryComposite): Boolean = op(t.left) < op(t) ||
    op(t.left) <= op(t) && op(t).assoc == LeftAssociative && op(t.left).assoc == LeftAssociative

  /**
   * Whether parentheses around `t.right` can be skipped because they are implied.
   * @note
   *   Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
   */
  protected override def skipParensRight(t: BinaryComposite): Boolean = op(t.right) < op(t) ||
    op(t.right) <= op(t) && op(t).assoc == RightAssociative && op(t.right).assoc == RightAssociative

}

/**
 * Weighted precedence-based: KeYmaera X Pretty Printer formats differential dynamic logic expressions with compact
 * brackets in KeYmaera X notation according and extra space weighted according to the concrete syntax of differential
 * dynamic logic with explicit statement end `;` operator.
 *
 * @author
 *   Andre Platzer
 * @see
 *   [[http://keymaeraX.org/doc/dL-grammar.md Grammar]]
 */
@deprecated("Use PrettierPrinter instead")
class KeYmaeraXWeightedPrettyPrinter extends KeYmaeraXPrecedencePrinter {

  // eloquent space if no parentheses
  protected override def wrapChild(t: Modal, childPrint: String): String =
    if (skipParens(t)) " " + childPrint else "(" + childPrint + ")"

  protected override def wrapLeft(t: BinaryComposite, leftPrint: String): String =
    if (skipParensLeft(t)) spaceLeft(t, leftPrint) else spaceLeft(t, "(" + leftPrint + ")")
  protected override def wrapRight(t: BinaryComposite, rightPrint: String): String =
    if (skipParensRight(t)) spaceRight(t, rightPrint) else spaceRight(t, "(" + rightPrint + ")")

  protected override def pwrapLeft(t: BinaryComposite /*Differential/Program*/, leftPrint: String): String =
    if (skipParensLeft(t)) spaceLeft(t, leftPrint) else spaceLeft(t, "{" + leftPrint + "}")
  protected override def pwrapRight(t: BinaryComposite /*Differential/Program*/, rightPrint: String): String =
    if (skipParensRight(t)) spaceRight(t, rightPrint) else spaceRight(t, "{" + rightPrint + "}")

  protected def spaceLeft(t: BinaryComposite, leftPrint: String): String =
    if (skipParensLeft(t)) leftPrint + (" " * weight(t.left, t)) else leftPrint
  protected def spaceRight(t: BinaryComposite, rightPrint: String): String =
    if (skipParensRight(t)) (" " * weight(t.right, t)) + rightPrint else rightPrint

  protected def weight(sub: Expression, par: BinaryComposite): Int = {
    val prec = op(par).prec
    if (prec >= 200)
      // programs are formatted relative to one another not with their ridiculously large prec
      (prec - 150) / 50
    else prec / 50
  }

  private def weight2(sub: Expression, par: BinaryComposite): Int = {
    val relative = Math.abs(op(sub).prec - op(par).prec)
    if (relative <= 10 /*|| !(binaryOfKind(par.left, par) || binaryOfKind(par.right, par))*/ ) 0 else relative / 20
  }

  /** Whether sub is a binary composite of the same kind that par is a binary composite */
  private def binaryOfKind(sub: Expression, par: BinaryComposite): Boolean = par.kind match {
    case TermKind => sub.isInstanceOf[BinaryCompositeTerm]
    case FormulaKind => sub.isInstanceOf[BinaryCompositeFormula]
    case ProgramKind => sub.isInstanceOf[BinaryCompositeProgram]
    case DifferentialProgramKind => sub.isInstanceOf[DifferentialProduct]
    case FunctionKind => assert(false, "No completed expressions of FunctionKind can be constructed"); ???
    case ExpressionKind => assert(false, "No expressions of ExpressionKind can be constructed"); ???
  }

  private def weight1(sub: Expression, par: BinaryComposite): Int = {
    val relative = Math.abs(op(sub).prec - op(par).prec)
    val imbalance = Math.abs(op(par.left).prec - op(par.right).prec)
    // @todo this implementation probably needs more thought
    if (relative < 10 || imbalance < 10) 0 else (relative + 19) / 20 // rounded-up division
  }

  override def stringify(e: Expression): String = super.stringify(e)
}

/** A pretty printer that omits the interpretations of interpreted functions. */
object KeYmaeraXOmitInterpretationPrettyPrinter extends KeYmaeraXOmitInterpretationPrettyPrinter

/** A pretty printer that omits the interpretations of interpreted functions. */
class KeYmaeraXOmitInterpretationPrettyPrinter extends KeYmaeraXPrecedencePrinter {
  override def apply(expr: Expression): String = stringify(expr) ensures
    (
      // @note functions and interpreted functions are printed without parentheses/interpretations and do not reparse
      r =>
        expr.kind == FunctionKind ||
          StaticSemantics
            .symbols(expr)
            .exists({
              case Function(_, _, _, _, i) => i.isDefined
              case _ => false
            }) || reparse(expr, r) == expr,
      "Expect parse of print to be identity." +
        // @todo reconcile first and last line of contract message
        "\nExpression: " + FullPrettyPrinter.stringify(expr) + "\t@ " + expr.getClass.getSimpleName + "\nPrinted:    " +
        stringify(expr) + "\nReparsed:   " + stringify(reparse(expr, stringify(expr))) + "\t@ " +
        reparse(expr, stringify(expr)).getClass.getSimpleName + "\nExpression: " +
        FullPrettyPrinter.stringify(reparse(expr, stringify(expr))) + "\t@ " +
        reparse(expr, stringify(expr)).getClass.getSimpleName + "\nExpected:   " + FullPrettyPrinter.stringify(expr) +
        "\t@ " + expr.getClass.getSimpleName,
    )

  protected override def pp(q: PosInExpr, term: Term): String = term match {
    case FuncOf(Function(n, i, _, _, Some(_)), Nothing) => emit(q, n + i.map("_" + _).getOrElse("") + "()")
    case FuncOf(Function(n, i, d, _, Some(_)), arg) =>
      if (d.isInstanceOf[Tuple]) emit(q, n + i.map("_" + _).getOrElse("") + pp(q ++ 0, arg))
      else emit(q, n + i.map("_" + _).getOrElse("") + "(" + pp(q ++ 0, arg) + ")")
    case FuncOf(f, Nothing) => emit(q, f.asString + "()")
    case _ => super.pp(q, term)
  }
}
