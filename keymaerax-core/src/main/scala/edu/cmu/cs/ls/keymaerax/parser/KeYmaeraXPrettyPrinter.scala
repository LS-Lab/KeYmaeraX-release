/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Differential Dynamic Logic pretty printer in concrete KeYmaera X notation.
 * @author Andre Platzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @note Code Review 2015-08-24
 */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.parser.OpSpec._
import edu.cmu.cs.ls.keymaerax.tactics.{HereP, PosInExpr}

import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Default KeYmaera X Pretty Printer formats differential dynamic logic expressions
 * @see [[edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrecedencePrinter]]
 */
object KeYmaeraXPrettyPrinter extends KeYmaeraXPrecedencePrinter {
  /** This default pretty printer. */
  val pp = this
}

/**
 * Vanilla: KeYmaera X Printer formats differential dynamic logic expressions
 * in KeYmaera X notation according to the concrete syntax of differential dynamic logic
 * with explicit statement end ``;`` operator.
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
class KeYmaeraXPrinter extends PrettyPrinter {

  import OpSpec.op
  import OpSpec.statementSemicolon

  /** Lax mode where the pretty-printer does not mind printing output that it can't parse the same way again. */
  private val LAX = System.getProperty("LAX", "false")=="true"

  /** Pretty-print term to a string */
  def apply(expr: Expression): String = stringify(expr) ensuring(
    r => LAX || expr.kind==FunctionKind || reparse(expr, r) == expr,
    "Parse of print is identity." +
      "\nExpression: " + fullPrinter(expr) + " @ " + expr.getClass.getSimpleName +
      "\nPrinted:    " + stringify(expr) +
      "\nReparsed:   " + reparse(expr, stringify(expr)) +
      "\nExpression: " + fullPrinter(reparse(expr, stringify(expr))) + " @ " + reparse(expr, stringify(expr)).getClass.getSimpleName +
      "\nExpected:   " + fullPrinter(expr) + " @ " + expr.getClass.getSimpleName
    )

  /** Pretty-print sequent to a string */
  def apply(seq: Sequent): String =
    (1 to seq.ante.length).map(i => -i + ":  " + apply(seq.ante(i-1)) + "\t" + seq.ante(i-1).getClass.getSimpleName).mkString("\n") +
      "\n  ==>  \n" +
      (1 to seq.succ.length).map(i => +i + ":  " + apply(seq.succ(i-1)) + "\t" + seq.succ(i-1).getClass.getSimpleName).mkString("\n")

  def parser: KeYmaeraXParser.type = KeYmaeraXParser
  def fullPrinter: (Expression => String) = FullPrettyPrinter


  /** Reparse the string print as the same kind as expr has */
  private def reparse(expr: Expression, print: String): Expression = expr.kind match {
    case TermKind => parser.termParser(print)
    case FormulaKind => parser.formulaParser(print)
    case ProgramKind => parser.programParser(print)
    case DifferentialProgramKind => parser.differentialProgramParser(print)
    case ExpressionKind => assert(false, "No expressions of ExpressionKind can be constructed"); ???
  }

  /** Pretty-print term to a string without contract checking. */
  private[parser] def stringify(expr: Expression) = expr match {
    case t: Term    => pp(HereP, t)
    case f: Formula => pp(HereP, f)
    case p: Program => pp(HereP, p)
    case f: Function => f.asString
  }

  /**
   * Whether parentheses around ``t.child`` can be skipped because they are implied.
   */
  protected def skipParens(t: UnaryComposite): Boolean = false
  protected def skipParens(t: Quantified): Boolean = false
  protected def skipParens(t: Modal): Boolean = false

  /**
   * Whether parentheses around ``t.left`` can be skipped because they are implied.
   * @note Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
   */
  protected def skipParensLeft(t: BinaryComposite): Boolean = false

  /**
   * Whether parentheses around ``t.right`` can be skipped because they are implied.
   * @note Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
   */
  protected def skipParensRight(t: BinaryComposite): Boolean = false

  private[parser] val negativeBrackets = false && OpSpec.negativeNumber

  /**@NOTE The extra space disambiguates x<-7 as in x < (-7) from x REVIMPLY 7 as well as x<-(x^2) from x REVIMPLY ... */
  private val LEXSPACE: String = " "

  //@todo could add contract that TermAugmentor(original)(q) == term
  private def pp(q: PosInExpr, term: Term): String = emit(q, term match {
    case DotTerm|Anything|Nothing=> op(term).opcode
    case x: Variable            => x.asString
    case DifferentialSymbol(x)  => pp(q+0, x) + op(term).opcode
    case Differential(t)        => "(" + pp(q+0, t) + ")" + op(term).opcode
      // special case forcing parentheses around numbers to avoid Neg(Times(Number(5),Variable("x")) to be printed as -5*x yet reparsed as (-5)*x. Alternatively could add space after unary Neg.
    case Number(n)              => if (negativeBrackets) {if (OpSpec.negativeNumber) "(" + n.toString() + ")"
      else assert(n>=0 || OpSpec.negativeNumber); n.toString()} else n.toString()
    case FuncOf(f, c)           => f.asString + "(" + pp(q+0, c) + ")"
    // special notation
    case Pair(l, r)             => "(" + pp(q+0, l) + op(term).opcode + pp(q+1, r) + ")"
    // special case forcing to disambiguate between -5 as in the number (-5) as opposed to -(5). OpSpec.negativeNumber
    case t@Neg(Number(n))       => op(t).opcode + "(" + pp(q+0, Number(n)) + ")"
    // special case forcing space between unary negation and numbers to avoid Neg(Times(Number(5),Variable("x")) to be printed as -5*x yet reparsed as (-5)*x.
    case t: Neg if !negativeBrackets => val c = pp(q+0, t.child); op(t).opcode + (if (c.charAt(0).isDigit) " " else "") + (if (skipParens(t)) c else "(" + c + ")")
    case t: UnaryCompositeTerm  => op(t).opcode + (if (skipParens(t)) pp(q+0, t.child) else "(" + pp(q+0, t.child) + ")")
    case t: BinaryCompositeTerm =>
      (if (skipParensLeft(t)) pp(q+0, t.left) else "(" + pp(q+0, t.left) + ")") +
        op(t).opcode +
        (if (skipParensRight(t)) pp(q+1, t.right) else "(" + pp(q+1, t.right) + ")")
  })

  private def pp(q: PosInExpr, formula: Formula): String = emit(q, formula match {
    case True|False|DotFormula  => op(formula).opcode
    case PredOf(p, c)           => p.asString + "(" + pp(q+0, c) + ")"
    case PredicationalOf(p, c)  => p.asString + "{" + pp(q+0, c) + "}"
    // special case to disambiguate between x<-y as in x < -y compared to x REVIMPLY y
    case f: Less                => pp(q+0, f.left) + LEXSPACE + op(formula).opcode + LEXSPACE + pp(q+1, f.right)
    case f: ComparisonFormula   => pp(q+0, f.left) + op(formula).opcode + pp(q+1, f.right)
    case DifferentialFormula(g) => "(" + pp(q+0, g) + ")" + op(formula).opcode
    //@note the q position for variables is a little weird since it identifies the quantifier not the variable
    case f: Quantified          => op(formula).opcode + " " + f.vars.map(pp(q,_)).mkString(",") + " " + (if (skipParens(f)) pp(q+0, f.child) else "(" + pp(q+0, f.child) + ")")
    case f: Box                 => "[" + pp(q+0, f.program) + "]" + (if (skipParens(f)) pp(q+1, f.child) else "(" + pp(q+1, f.child) + ")")
    case f: Diamond             => "<" + pp(q+0, f.program) + ">" + (if (skipParens(f)) pp(q+1, f.child) else "(" + pp(q+1, f.child) + ")")
    case t: UnaryCompositeFormula=> op(t).opcode + (if (skipParens(t)) pp(q+0, t.child) else "(" + pp(q+0, t.child) + ")")
    case t: BinaryCompositeFormula=>
      (if (skipParensLeft(t)) pp(q+0, t.left) else "(" + pp(q+0, t.left) + ")") +
        op(t).opcode +
        (if (skipParensRight(t)) pp(q+1, t.right) else "(" + pp(q+1, t.right) + ")")
  })

  private def pp(q: PosInExpr, program: Program): String = emit(q, program match {
    case a: ProgramConst        => statement(a.asString)
    case Assign(x, e)           => statement(pp(q+0, x) + op(program).opcode + pp(q+1, e))
    case DiffAssign(xp, e)      => statement(pp(q+0, xp) + op(program).opcode + pp(q+1, e))
    case AssignAny(x)           => statement(pp(q+0, x) + op(program).opcode)
    case Test(f)                => statement(op(program).opcode + pp(q+0, f))
    case ODESystem(ode, f)      => "{" + ppODE(q+0, ode) + (if (false && f==True) "" else op(program).opcode + pp(q+1, f)) + "}"
    //@note unambiguously reparse as ODE not as equation that happens to involve a differential symbol.
    //@note This is only used in printing internal data structures, not user input.
    //@note no positional change since only internal data structure swap-over
    case ode: DifferentialProgram => "{" + ppODE(q, ode) + "}"
    //@note forced parentheses in grammar for loops and duals
    case t: UnaryCompositeProgram => "{" + pp(q+0, t.child) + "}" + op(program).opcode
    //case t: UnaryCompositeProgram=> (if (skipParens(t)) pp(t.child) else "{" + pp(t.child) + "}") + op(program).opcode
    case t: Compose if OpSpec.statementSemicolon =>
      //@note in statementSemicolon mode, suppress opcode of Compose since already after each statement
      (if (skipParensLeft(t)) pp(q+0, t.left) else "{" + pp(q+0, t.left) + "}") +
        /*op(t).opcode + */
        (if (skipParensRight(t)) pp(q+1, t.right) else "{" + pp(q+1, t.right) + "}")
    case t: BinaryCompositeProgram =>
      (if (skipParensLeft(t)) pp(q+0, t.left) else "{" + pp(q+0, t.left) + "}") +
        op(t).opcode +
        (if (skipParensRight(t)) pp(q+1, t.right) else "{" + pp(q+1, t.right) + "}")
  })

  private def ppODE(q: PosInExpr, program: DifferentialProgram): String = emit(q, program match {
    case a: DifferentialProgramConst => a.asString
    case AtomicODE(xp, e)       => pp(q+0, xp) + op(program).opcode + pp(q+1, e)
    case t: DifferentialProduct =>
      (if (skipParensLeft(t)) ppODE(q+0, t.left) else "{" + ppODE(q+1, t.left) + "}") +
        op(t).opcode +
        (if (skipParensRight(t)) ppODE(q+1, t.right) else "{" + ppODE(q+1, t.right) + "}")
    case ODESystem(ode, f)      => assert(false, "ODESystem does not occur recursively"); ??? //{" + ppODE(ode) + op(program).opcode + pp(f) + "}"
  })

  /** Emit the string s as a result of the pretty-printer for an expression */
  protected def emit(q: PosInExpr, s: String): String = s

  /** Formatting the atomic statement s */
  private def statement(s: String): String = if (statementSemicolon) s + ";" else s

}

/**
 * Precedence-based: KeYmaera X Pretty Printer formats differential dynamic logic expressions with compact brackets
 * in KeYmaera X notation according to the concrete syntax of differential dynamic logic
 * with explicit statement end ``;`` operator.
 * @author Andre Platzer
 * @todo Augment with ensuring postconditions that check correct reparse non-recursively.
 * @see doc/dL-grammar.md
 */
class KeYmaeraXPrecedencePrinter extends KeYmaeraXPrinter {
  protected override def skipParens(t: UnaryComposite): Boolean = op(t.child) <= op(t)
  protected override def skipParens(t: Quantified): Boolean = op(t.child) <= op(t)
  protected override def skipParens(t: Modal): Boolean = op(t.child) <= op(t)

  /**
   * Whether parentheses around ``t.left`` can be skipped because they are implied.
   * @note Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
   */
  protected override def skipParensLeft(t: BinaryComposite): Boolean =
    op(t.left) < op(t) || op(t.left) <= op(t) && op(t).assoc == LeftAssociative && op(t.left).assoc == LeftAssociative

  /**
   * Whether parentheses around ``t.right`` can be skipped because they are implied.
   * @note Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
   */
  protected override def skipParensRight(t: BinaryComposite): Boolean =
    op(t.right) < op(t) || op(t.right) <= op(t) && op(t).assoc == RightAssociative && op(t.right).assoc == RightAssociative

}

/**
 * Fully-parenthesized pretty printer in full form with full parentheses.
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
object FullPrettyPrinter extends KeYmaeraXPrinter {
  //@note no contract to avoid recursive checking of contracts in error messages of KeYmaeraXPrinter.apply
  override def apply(expr: Expression): String = stringify(expr)
}