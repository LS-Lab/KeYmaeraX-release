/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Differential Dynamic Logic pretty printer in concrete KeYmaera X notation.
  *
  * @author Andre Platzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @note Code Review 2016-08-02
 */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.parser.OpSpec.op
import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr
import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr.HereP

import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Default KeYmaera X Pretty Printer formats differential dynamic logic expressions
  *
  * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrecedencePrinter]]
 */
object KeYmaeraXPrettyPrinter extends KeYmaeraXPrecedencePrinter {
  /** This default pretty printer. */
  val pp = this
}

/**
  * Common base functionality for KeYmaera X Pretty Printers.
  */
trait BasePrettyPrinter extends PrettyPrinter {

  /** Pretty-print term to a string */
  def apply(expr: Expression): String = stringify(expr) ensuring(
    r => expr.kind == FunctionKind || reparse(expr, r) == expr,
    "Parse of print is identity." +
      "\nExpression: " + FullPrettyPrinter.stringify(expr) + "\t@ " + expr.getClass.getSimpleName +
      "\nPrinted:    " + stringify(expr) +
      "\nReparsed:   " + stringify(reparse(expr, stringify(expr))) + "\t@ " + reparse(expr, stringify(expr)).getClass.getSimpleName +
      "\nExpression: " + FullPrettyPrinter.stringify(reparse(expr, stringify(expr))) + "\t@ " + reparse(expr, stringify(expr)).getClass.getSimpleName +
      "\nExpected:   " + FullPrettyPrinter.stringify(expr) + "\t@ " + expr.getClass.getSimpleName
    )

  /** Pretty-print sequent to a string */
  def apply(seq: Sequent): String =
    (1 to seq.ante.length).map(i => -i + ":  " + apply(seq.ante(i - 1)) + "\t" + seq.ante(i - 1).getClass.getSimpleName).mkString("\n") +
      "\n  ==>  \n" +
      (1 to seq.succ.length).map(i => +i + ":  " + apply(seq.succ(i - 1)) + "\t" + seq.succ(i - 1).getClass.getSimpleName).mkString("\n")

  /** Pretty-print sequent to a string but without contract checking! */
  private[keymaerax] def stringify(seq: Sequent): String =
    (1 to seq.ante.length).map(i => -i + ":  " + stringify(seq.ante(i - 1)) + "\t" + seq.ante(i - 1).getClass.getSimpleName).mkString("\n") +
      "\n  ==>  \n" +
      (1 to seq.succ.length).map(i => +i + ":  " + stringify(seq.succ(i - 1)) + "\t" + seq.succ(i - 1).getClass.getSimpleName).mkString("\n")

  /** Reparse the string print as the same kind as expr has */
  private def reparse(expr: Expression, print: String): Expression = expr.kind match {
    case TermKind => parser.termParser(print)
    case FormulaKind => parser.formulaParser(print)
    case ProgramKind => parser.programParser(print)
    case DifferentialProgramKind => parser.differentialProgramParser(print)
    case ExpressionKind => assert(false, "No expressions of ExpressionKind can be constructed"); ???
  }

  /** Pretty-print term to a string but without contract checking! */
  private[keymaerax] def stringify(expr: Expression): String
}

/**
  * Fully-parenthesized pretty printer in full form with full parentheses.
  *
  * @example
  * Fully parenthesized strings are obtained using the [[edu.cmu.cs.ls.keymaerax.parser.FullPrettyPrinter]] printer:
  * {{{
  * val pp = FullPrettyPrinter
  * // "x < -(y)"
  * val fml0 = Less(Variable("x"),Neg(Variable("y")))
  * val fml0str = pp(fml0)
  * // "true -> ([x:=1;](x>=0))"
  * val fml1 = Imply(True, Box(Assign(Variable("x"), Number(1)), GreaterEqual(Variable("x"), Number(0))))
  * val fml1str = pp(fml1)
  * }}}
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrinter.fullPrinter]]
  */
object FullPrettyPrinter extends BasePrettyPrinter {

  import OpSpec.op
  import OpSpec.statementSemicolon

  val parser: KeYmaeraXParser.type = KeYmaeraXParser
  val fullPrinter: (Expression => String) = this


  /** Pretty-print term to a string but without contract checking! */
  private[keymaerax] def stringify(expr: Expression): String = expr match {
    case t: Term    => pp(t)
    case f: Formula => pp(f)
    case p: Program => pp(p)
    case f: Function => f.asString
  }

  /**@note The extra space disambiguates x<-7 as in x < (-7) from x REVIMPLY 7 as well as x<-(x^2) from x REVIMPLY ... */
  private val LEXSPACE: String = " "

  private def pp(term: Term): String = term match {
    case Nothing       => op(term).opcode
    case DotTerm(sort) => op(term).opcode + (sort match { case Tuple(_, _) => sort.toString case _ => "" }) //@note will parse as Pair(Variable("Real"), ...), which has Sort sort
    case x: Variable            => x.asString
    case DifferentialSymbol(x)  => pp(x) + op(term).opcode
    case Differential(t)        => "(" + pp(t) + ")" + op(term).opcode
    // forcing parentheses around numbers to avoid Neg(Times(Number(5),Variable("x")) to be printed as -5*x yet reparsed as (-5)*x. Alternatively could add space after unary Neg.
    case Number(n)              => "(" + n.toString() + ")"
    case FuncOf(f, c)           => f.asString + "(" + pp(c) + ")"
    // special notation
    case Pair(l, r)             => "(" + pp(l) + op(term).opcode + pp(r) + ")"
    case UnitFunctional(name,space,sort) => name + "(" + space + ")"
    case t: UnaryCompositeTerm  => op(t).opcode + "(" + pp(t.child) + ")"
    case t: BinaryCompositeTerm =>
      "(" + pp(t.left) + ")" + op(t).opcode + "(" + pp(t.right) + ")"
  }

  private def pp(formula: Formula): String = formula match {
    case True|False|DotFormula  => op(formula).opcode
    case PredOf(p, c)           => p.asString + "(" + pp(c) + ")"
    case PredicationalOf(p, c)  => p.asString + "{" + pp(c) + "}"
    case f: ComparisonFormula   => "(" + pp(f.left) + ")" + LEXSPACE + op(formula).opcode + LEXSPACE + "(" + pp(f.right) + ")"
    case DifferentialFormula(g) => "(" + pp(g) + ")" + op(formula).opcode
    //@note the q position for variables is a little weird since it identifies the quantifier not the variable
    case f: Quantified          => op(formula).opcode + " " + f.vars.map(pp).mkString(",") + " " + "(" + pp(f.child) + ")"
    case f: Box                 => "[" + pp(f.program) + "]" + "(" + pp(f.child) + ")"
    case f: Diamond             => "<" + pp(f.program) + ">" + "(" + pp(f.child) + ")"
    case UnitPredicational(name,space) => name + "(" + space + ")"
    case t: UnaryCompositeFormula=> op(t).opcode + "(" + pp(t.child) + ")"
    case t: BinaryCompositeFormula=>
      "(" + pp(t.left) + ")" + op(t).opcode + "(" + pp(t.right) + ")"
  }

  private def pp(program: Program): String = program match {
    case a: ProgramConst        => statement(a.asString)
    case a: SystemConst         => statement(a.toString)
    case Assign(x, e)           => statement(pp(x) + op(program).opcode + pp(e))
    //case DiffAssign(xp, e)      => statement(pp(xp) + op(program).opcode + pp(e))
    case AssignAny(x)           => statement(pp(x) + op(program).opcode)
    case Test(f)                => statement(op(program).opcode + "(" + pp(f) + ")")
    case ODESystem(ode, f)      => "{" + ppODE(ode) + op(program).opcode + pp(f) + "}"
    //@note unambiguously reparse as ODE not as equation that happens to involve a differential symbol.
    //@note This is only used in printing internal data structures, not user input.
    //@note no positional change since only internal data structure swap-over
    case ode: DifferentialProgram => "{" + ppODE(ode) + "}"
    case t: UnaryCompositeProgram => "{" + pp(t.child) + "}" + op(program).opcode
//    case t: Compose if OpSpec.statementSemicolon =>
//      //@note in statementSemicolon mode, suppress opcode of Compose since already after each statement
//      "{" + pp(t.left) + "}" + /*op(t).opcode + */ "{" + pp(t.right) + "}"
    case t: BinaryCompositeProgram =>
      "{" + pp(t.left) + "}" + op(t).opcode + "{" + pp(t.right) + "}"
  }

  private def ppODE(program: DifferentialProgram): String = program match {
    case a: DifferentialProgramConst => a.asString
    case AtomicODE(xp, e)       => pp(xp) + op(program).opcode + pp(e)
    case t: DifferentialProduct =>
      assert(op(t).assoc==RightAssociative && !t.left.isInstanceOf[DifferentialProduct], "differential products are always right-associative")
      ppODE(t.left) + op(t).opcode + ppODE(t.right)
  }


  /** Formatting the atomic statement s */
  private def statement(s: String): String = if (statementSemicolon) s + ";" else s

}

/**
 * Vanilla: KeYmaera X Printer formats differential dynamic logic expressions
 * in KeYmaera X notation according to the concrete syntax of differential dynamic logic
 * with explicit statement end ``;`` operator.
  *
  * @example
 * Printing formulas to strings is straightforward using [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter.apply]]:
 * {{{
 * val pp = KeYmaeraXPrettyPrinter
 * // "x < -y"
 * val fml0 = Less(Variable("x"),Neg(Variable("y")))
 * val fml0str = pp(fml0)
 * // "true -> [x:=1;]x>=0"
 * val fml1 = Imply(True, Box(Assign(Variable("x"), Number(1)), GreaterEqual(Variable("x"), Number(0))))
 * val fml1str = pp(fml1)
 * }}}
 * @author Andre Platzer
 * @todo Augment with ensuring postconditions that check correct reparse non-recursively.
 * @see [[http://keymaeraX.org/doc/dL-grammar.md Grammar]]
 */
class KeYmaeraXPrinter extends BasePrettyPrinter {

  import OpSpec.op
  import OpSpec.statementSemicolon

  val parser: KeYmaeraXParser.type = KeYmaeraXParser
  val fullPrinter: (Expression => String) = FullPrettyPrinter

  /** Pretty-print term to a string but without contract checking! */
  private[keymaerax] def stringify(expr: Expression) = expr match {
    case t: Term    => pp(HereP, t)
    case f: Formula => pp(HereP, f)
    case p: Program => pp(HereP, p)
    case f: Function => f.asString
  }

  /** True if negative numbers should get extra parentheses */
  private[parser] val negativeBrackets = false && OpSpec.negativeNumber

  /**@note The extra space disambiguates x<-7 as in x < (-7) from x REVIMPLY 7 as well as x<-(x^2) from x REVIMPLY ... */
  private val LEXSPACE: String = " "

  //@todo could add contract that TermAugmentor(original)(q) == term
  protected def pp(q: PosInExpr, term: Term): String = emit(q, term match {
    case Nothing       => op(term).opcode
    case DotTerm(sort) => op(term).opcode + (sort match { case Tuple(_, _) => sort.toString case _ => "" }) //@note will parse as Pair(Variable("Real"), ...), which has Sort sort
    case x: Variable            => x.asString
    case DifferentialSymbol(x)  => x.asString + op(term).opcode
    case Differential(t)        => "(" + pp(q++0, t) + ")" + op(term).opcode
      // special case forcing parentheses around numbers to avoid Neg(Times(Number(5),Variable("x")) to be printed as -5*x yet reparsed as (-5)*x. Alternatively could add space after unary Neg.
    case Number(n)              => if (negativeBrackets) {
      if (OpSpec.negativeNumber) "(" + n.toString() + ")"
      else assert(n>=0 || OpSpec.negativeNumber); n.toString()
    } else n.toString()
    case FuncOf(f, c)           => f.asString + "(" + pp(q++0, c) + ")"
    // special notation
    case Pair(l, r)             => "(" + pp(q++0, l) + op(term).opcode + pp(q++1, r) + ")"
    case UnitFunctional(name,space,sort) => name + "(" + space + ")"
    // special case forcing to disambiguate between -5 as in the number (-5) as opposed to -(5). OpSpec.negativeNumber
    case t@Neg(Number(n))       => op(t).opcode + "(" + pp(q++0, Number(n)) + ")"
    // special case forcing space between unary negation and numbers to avoid Neg(Times(Number(5),Variable("x")) to be printed as -5*x yet reparsed as (-5)*x.
    case t: Neg if !negativeBrackets => val c = pp(q++0, t.child)
      op(t).opcode + (if (c.charAt(0).isDigit) " " else "") + wrapChild(t, c)
    case t: UnaryCompositeTerm  => op(t).opcode + wrapChild(t, pp(q++0, t.child))
    case t: BinaryCompositeTerm =>
      wrapLeft(t, pp(q++0, t.left)) + op(t).opcode + wrapRight(t, pp(q++1, t.right))
  })

  private def pp(q: PosInExpr, formula: Formula): String = emit(q, formula match {
    case True|False|DotFormula  => op(formula).opcode
    case PredOf(p, c)           => p.asString + "(" + pp(q++0, c) + ")"
    case PredicationalOf(p, c)  => p.asString + "{" + pp(q++0, c) + "}"
    // special case to disambiguate between x<-y as in x < -y compared to x REVIMPLY y
    case f: Less                => wrapLeft(f, pp(q++0, f.left)) + LEXSPACE + op(formula).opcode + LEXSPACE + wrapRight(f, pp(q++1, f.right))
    case f: ComparisonFormula   => wrapLeft(f, pp(q++0, f.left)) + op(formula).opcode + wrapRight(f, pp(q++1, f.right))
    case DifferentialFormula(g) => "(" + pp(q++0, g) + ")" + op(formula).opcode
    //@note the q position for variables is a little weird since it identifies the quantifier not the variable
    case f: Quantified          => op(formula).opcode + " " + f.vars.map(pp(q,_)).mkString(",") + " " + wrapChild(f, pp(q++0, f.child))
    case f: Box                 => "[" + pp(q++0, f.program) + "]" + wrapChild(f, pp(q++1, f.child))
    case f: Diamond             => "<" + pp(q++0, f.program) + ">" + wrapChild(f, pp(q++1, f.child))
    case UnitPredicational(name,space) => name + "(" + space + ")"
    case t: UnaryCompositeFormula=> op(t).opcode + wrapChild(t, pp(q++0, t.child))
    case t: BinaryCompositeFormula=>
      wrapLeft(t, pp(q++0, t.left)) + op(t).opcode + wrapRight(t, pp(q++1, t.right))
  })

  private def pp(q: PosInExpr, program: Program): String = emit(q, program match {
    case a: ProgramConst        => statement(a.asString)
    case a: SystemConst         => statement(a.toString)
    case Assign(x, e)           => statement(pp(q++0, x) + op(program).opcode + pp(q++1, e))
    //case DiffAssign(xp, e)      => statement(pp(q++0, xp) + op(program).opcode + pp(q++1, e))
    case AssignAny(x)           => statement(pp(q++0, x) + op(program).opcode)
    case Test(f)                => statement(op(program).opcode + pp(q++0, f))
    case ODESystem(ode, f)      => "{" + ppODE(q++0, ode) + (if (false && f==True) "" else op(program).opcode + pp(q++1, f)) + "}"
    //@note unambiguously reparse as ODE not as equation that happens to involve a differential symbol.
    //@note This is only used in printing internal data structures, not user input.
    //@note no positional change since only internal data structure swap-over
    case ode: DifferentialProgram => "{" + ppODE(q, ode) + "}"
    //@note forced parentheses in grammar for loops and duals
    case t: UnaryCompositeProgram => "{" + pp(q++0, t.child) + "}" + op(program).opcode
    //case t: UnaryCompositeProgram=> (if (skipParens(t)) pp(t.child) else "{" + pp(t.child) + "}") + op(program).opcode
    case t: Compose if OpSpec.statementSemicolon =>
      //@note in statementSemicolon mode, suppress opcode of Compose since already after each statement
      pwrapLeft(t, pp(q++0, t.left)) + /*op(t).opcode + */ pwrapRight(t, pp(q++1, t.right))
    case t: BinaryCompositeProgram =>
      pwrapLeft(t, pp(q++0, t.left)) + op(t).opcode + pwrapRight(t, pp(q++1, t.right))
  })

  private def ppODE(q: PosInExpr, program: DifferentialProgram): String = emit(q, program match {
    case a: DifferentialProgramConst => a.asString
    case AtomicODE(xp, e)       => pp(q++0, xp) + op(program).opcode + pp(q++1, e)
    case t: DifferentialProduct =>
      assert(op(t).assoc==RightAssociative && !t.left.isInstanceOf[DifferentialProduct], "differential products are always right-associative")
      ppODE(q++0, t.left) + op(t).opcode + ppODE(q++1, t.right)
  })


  // parentheses wrapping and emission

  /** Wrap ``childPrint`` for ``t.child`` in parentheses if they are not implicit. */
  protected def wrapChild(t: UnaryComposite, childPrint: String): String = "(" + childPrint + ")"
  /** Wrap ``childPrint`` for ``t.child`` in parentheses if they are not implicit. */
  protected def wrapChild(t: Quantified, childPrint: String): String = "(" + childPrint + ")"
  /** Wrap ``childPrint`` for ``t.child`` in parentheses if they are not implicit. */
  protected def wrapChild(t: Modal, childPrint: String): String = "(" + childPrint + ")"

  /** Wrap ``leftPrint`` for ``t.left`` in parentheses if they are not implicit. */
  protected def wrapLeft(t: BinaryComposite, leftPrint: String): String = "(" + leftPrint + ")"
  /** Wrap ``rightPrint`` for ``t.right`` in parentheses if they are not implicit. */
  protected def wrapRight(t: BinaryComposite, rightPrint: String): String = "(" + rightPrint + ")"

//  /** Wrap ``leftPrint`` for ``t.left`` in parentheses if they are not implicit. */
//  protected def wrapLeft(t: ComparisonFormula, leftPrint: String): String = "(" + leftPrint + ")"
//  /** Wrap ``rightPrint`` for ``t.right`` in parentheses if they are not implicit. */
//  protected def wrapRight(t: ComparisonFormula, rightPrint: String): String = "(" + rightPrint + ")"

  /** Wrap ``leftPrint`` for ``t.left`` in program parentheses if they are not implicit. */
  protected def pwrapLeft(t: BinaryComposite/*Differential/Program*/, leftPrint: String): String =
    "{" + leftPrint + "}"
  /** Wrap ``rightPrint`` for ``t.right`` in program parentheses if they are not implicit. */
  protected def pwrapRight(t: BinaryComposite/*Differential/Program*/, rightPrint: String): String =
    "{" + rightPrint + "}"

  /** Emit the string ``s`` as a result of the pretty-printer for the expression at position ``q`` */
  protected def emit(q: PosInExpr, s: String): String = s

  /** Formatting the atomic statement s */
  private def statement(s: String): String = if (statementSemicolon) s + ";" else s

}

// additional pretty printers


/** Fully parenthesized pretty printer that is functionally equivalent to [[FullPrettyPrinter]] */
object FullPrettyPrinter0 extends KeYmaeraXPrinter {
  //@note no contract to avoid recursive checking of contracts in error messages of KeYmaeraXPrinter.apply
  override def apply(expr: Expression): String = stringify(expr)
}

/**
  * KeYmaera X Printer base class formatting based on parentheses skipping decisions.
  *
  * @author Andre Platzer
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

  protected override def pwrapLeft(t: BinaryComposite/*Differential/Program*/, leftPrint: String): String =
    if (skipParensLeft(t)) leftPrint else "{" + leftPrint + "}"
  protected override def pwrapRight(t: BinaryComposite/*Differential/Program*/, rightPrint: String): String =
    if (skipParensRight(t)) rightPrint else "{" + rightPrint + "}"

  /**
    * Whether parentheses around ``t.child`` can be skipped because they are implicit.
    *
    * @see [[wrapChild()]]
    */
  protected def skipParens(t: UnaryComposite): Boolean
  protected def skipParens(t: Quantified): Boolean
  protected def skipParens(t: Modal): Boolean

  /**
    * Whether parentheses around ``t.left`` can be skipped because they are implicit.
    *
    * @note Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
    * @see [[wrapLeft()]]
    */
  protected def skipParensLeft(t: BinaryComposite): Boolean

  /**
    * Whether parentheses around ``t.right`` can be skipped because they are implicit.
    *
    * @note Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
    * @see [[wrapRight()]]
    */
  protected def skipParensRight(t: BinaryComposite): Boolean

}

/**
 * Precedence-based: KeYmaera X Pretty Printer formats differential dynamic logic expressions with compact brackets
 * in KeYmaera X notation according to the concrete syntax of differential dynamic logic
 * with explicit statement end ``;`` operator.
  *
  * @author Andre Platzer
 * @todo Augment with ensuring postconditions that check correct reparse non-recursively.
 * @see [[http://keymaeraX.org/doc/dL-grammar.md Grammar]]
 */
class KeYmaeraXPrecedencePrinter extends KeYmaeraXSkipPrinter {
  protected override def skipParens(t: UnaryComposite): Boolean = op(t.child) <= op(t)
  protected override def skipParens(t: Quantified): Boolean = op(t.child) <= op(t)
  protected override def skipParens(t: Modal): Boolean = op(t.child) <= op(t)

  /**
   * Whether parentheses around ``t.left`` can be skipped because they are implied.
    *
    * @note Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
   */
  protected override def skipParensLeft(t: BinaryComposite): Boolean =
    op(t.left) < op(t) || op(t.left) <= op(t) && op(t).assoc == LeftAssociative && op(t.left).assoc == LeftAssociative

  /**
   * Whether parentheses around ``t.right`` can be skipped because they are implied.
    *
    * @note Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
   */
  protected override def skipParensRight(t: BinaryComposite): Boolean =
    op(t.right) < op(t) || op(t.right) <= op(t) && op(t).assoc == RightAssociative && op(t.right).assoc == RightAssociative

}

/**
  * Weighted precedence-based: KeYmaera X Pretty Printer formats differential dynamic logic expressions with compact brackets
  * in KeYmaera X notation according and extra space weighted according to the concrete syntax of differential dynamic logic
  * with explicit statement end ``;`` operator.
  *
  * @author Andre Platzer
  * @see [[http://keymaeraX.org/doc/dL-grammar.md Grammar]]
  */
class KeYmaeraXWeightedPrettyPrinter extends KeYmaeraXPrecedencePrinter {

  // eloquent space if no parentheses
  protected override def wrapChild(t: Modal, childPrint: String): String =
    if (skipParens(t)) " " + childPrint else "(" + childPrint + ")"

  protected override def wrapLeft(t: BinaryComposite, leftPrint: String): String =
    if (skipParensLeft(t)) spaceLeft(t, leftPrint) else spaceLeft(t, "(" + leftPrint + ")")
  protected override def wrapRight(t: BinaryComposite, rightPrint: String): String =
    if (skipParensRight(t)) spaceRight(t, rightPrint) else spaceRight(t, "(" + rightPrint + ")")

  protected override def pwrapLeft(t: BinaryComposite/*Differential/Program*/, leftPrint: String): String =
    if (skipParensLeft(t)) spaceLeft(t, leftPrint) else spaceLeft(t, "{" + leftPrint + "}")
  protected override def pwrapRight(t: BinaryComposite/*Differential/Program*/, rightPrint: String): String =
    if (skipParensRight(t)) spaceRight(t, rightPrint) else spaceRight(t, "{" + rightPrint + "}")

  protected def spaceLeft(t: BinaryComposite, leftPrint: String): String =
    if (skipParensLeft(t)) leftPrint + (" " * weight(t.left, t)) else leftPrint
  protected def spaceRight(t: BinaryComposite, rightPrint: String): String =
    if (skipParensRight(t)) (" " * weight(t.right, t)) + rightPrint else rightPrint

  protected def weight(sub: Expression, par: BinaryComposite): Int = {
    val prec = op(par).prec
    if (prec >= 200)
      // programs are formatted relative to one another not with their ridiculously large prec
      (prec-150) / 50
    else
      prec / 50
  }

  private def weight2(sub: Expression, par: BinaryComposite): Int = {
    val relative = Math.abs(op(sub).prec - op(par).prec)
    if (relative <= 10 /*|| !(binaryOfKind(par.left, par) || binaryOfKind(par.right, par))*/) 0
    else relative / 20
  }

  /** Whether sub is a binary composite of the same kind that par is a binary composite */
  private def binaryOfKind(sub: Expression, par: BinaryComposite): Boolean = par.kind match {
    case TermKind => sub.isInstanceOf[BinaryCompositeTerm]
    case FormulaKind => sub.isInstanceOf[BinaryCompositeFormula]
    case ProgramKind => sub.isInstanceOf[BinaryCompositeProgram]
    case DifferentialProgramKind => sub.isInstanceOf[DifferentialProduct]
  }

  private def weight1(sub: Expression, par: BinaryComposite): Int = {
    val relative = Math.abs(op(sub).prec - op(par).prec)
    val imbalance = Math.abs(op(par.left).prec - op(par.right).prec)
    //@todo this implementation probably needs more thought
    if (relative<10 || imbalance<10) 0
    else (relative + 19) / 20    // rounded-up division
  }

  override def stringify(e: Expression): String = super.stringify(e)
}
