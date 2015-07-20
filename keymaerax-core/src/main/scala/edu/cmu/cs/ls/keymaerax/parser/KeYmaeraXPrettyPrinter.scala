/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Differential Dynamic Logic pretty printer in concrete KeYmaera X notation.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser
import edu.cmu.cs.ls.keymaerax.parser.OpSpec._

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
 * @author aplatzer
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

  def parser: KeYmaeraXParser.type = KeYmaeraXParser
  def fullPrinter: (Expression => String) = FullPrettyPrinter


  /** Reparse the string print as the same kind as expr has */
  private def reparse(expr: Expression, print: String): Expression = expr.kind match {
    case TermKind => parser.termParser(print)
    case FormulaKind => parser.formulaParser(print)
    case ProgramKind => parser.programParser(print)
    case DifferentialProgramKind => parser.differentialProgramParser(print)
  }

  /** Pretty-print term to a string without contract checking. */
  private[parser] def stringify(expr: Expression) = expr match {
    case t: Term => pp(t)
    case f: Formula => pp(f)
    case p: Program => pp(p)
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

  /**@NOTE The extra space disambiguates x<-7 as in x < (-7) from x REVIMPLY 7 as well as x<-(x^2) from x REVIMPLY ... */
  private val LEXSPACE: String = " "

  private def pp(term: Term): String = term match {
    case DotTerm|Anything|Nothing=> op(term).opcode
    case x: Variable            => x.asString
    case DifferentialSymbol(x)  => pp(x) + op(term).opcode
    case Differential(t)        => "(" + pp(t) + ")" + op(term).opcode
    case Number(n)              => n.toString()
    case FuncOf(f, c)           => f.asString + "(" + pp(c) + ")"
    // special notation
    case Pair(l, r)             => "(" + pp(l) + op(term).opcode + pp(r) + ")"
    // special case forcing to disambiguate between -5 as in the number (-5) as opposed to -(5).
    case t@Neg(Number(n))       => op(t).opcode + "(" + pp(Number(n)) + ")"
    case t: UnaryCompositeTerm  => op(t).opcode + (if (skipParens(t)) pp(t.child) else "(" + pp(t.child) + ")")
    case t: BinaryCompositeTerm =>
      (if (skipParensLeft(t)) pp(t.left) else "(" + pp(t.left) + ")") +
        op(t).opcode +
        (if (skipParensRight(t)) pp(t.right) else "(" + pp(t.right) + ")")
  }

  private def pp(formula: Formula): String = formula match {
    case True|False|DotFormula  => op(formula).opcode
    case PredOf(p, c)           => p.asString + "(" + pp(c) + ")"
    case PredicationalOf(p, c)  => p.asString + "{" + pp(c) + "}"
    // special case to disambiguate between x<-y as in x < -y compared to x REVIMPLY y
    case f: Less                => pp(f.left) + LEXSPACE + op(formula).opcode + LEXSPACE + pp(f.right)
    case f: ComparisonFormula   => pp(f.left) + op(formula).opcode + pp(f.right)
    case DifferentialFormula(g) => "(" + pp(g) + ")" + op(formula).opcode
    case f: Quantified          => op(formula).opcode + " " + f.vars.map(pp).mkString(",") + " " + (if (skipParens(f)) pp(f.child) else "(" + pp(f.child) + ")")
    case f: Box                 => "[" + pp(f.program) + "]" + (if (skipParens(f)) pp(f.child) else "(" + pp(f.child) + ")")
    case f: Diamond             => "<" + pp(f.program) + ">" + (if (skipParens(f)) pp(f.child) else "(" + pp(f.child) + ")")
    case t: UnaryCompositeFormula=> op(t).opcode + (if (skipParens(t)) pp(t.child) else "(" + pp(t.child) + ")")
    case t: BinaryCompositeFormula=>
      (if (skipParensLeft(t)) pp(t.left) else "(" + pp(t.left) + ")") +
        op(t).opcode +
        (if (skipParensRight(t)) pp(t.right) else "(" + pp(t.right) + ")")
  }

  private def pp(program: Program): String = program match {
    case a: ProgramConst        => statement(a.asString)
    case Assign(x, e)           => statement(pp(x) + op(program).opcode + pp(e))
    case AssignAny(x)           => statement(pp(x) + op(program).opcode)
    case DiffAssign(xp, e)      => statement(pp(xp) + op(program).opcode + pp(e))
    case Test(f)                => statement(op(program).opcode + pp(f))
    case ODESystem(ode, f)      => "{" + ppODE(ode) + (if (false && f==True) "" else op(program).opcode + pp(f)) + "}"
    //@note unambiguously reparse as ODE not as equation that happens to involve a differential symbol.
    //@note This is only used in printing internal data structures, not user input.
    case ode: DifferentialProgram => "{" + ppODE(ode) + "}"
    //@note forced parentheses in grammar for loops and duals
    case t: UnaryCompositeProgram => "{" + pp(t.child) + "}" + op(program).opcode
    //case t: UnaryCompositeProgram=> (if (skipParens(t)) pp(t.child) else "{" + pp(t.child) + "}") + op(program).opcode
    case t: Compose if OpSpec.statementSemicolon =>
      (if (skipParensLeft(t)) pp(t.left) else "{" + pp(t.left) + "}") +
        /*op(t).opcode + */
        (if (skipParensRight(t)) pp(t.right) else "{" + pp(t.right) + "}")
    case t: BinaryCompositeProgram =>
      (if (skipParensLeft(t)) pp(t.left) else "{" + pp(t.left) + "}") +
        op(t).opcode +
        (if (skipParensRight(t)) pp(t.right) else "{" + pp(t.right) + "}")
  }

  private def ppODE(program: DifferentialProgram): String = program match {
    case a: DifferentialProgramConst => a.asString
    case AtomicODE(xp, e)       => pp(xp) + op(program).opcode + pp(e)
    case t: DifferentialProduct =>
      (if (skipParensLeft(t)) ppODE(t.left) else "{" + ppODE(t.left) + "}") +
        op(t).opcode +
        (if (skipParensRight(t)) ppODE(t.right) else "{" + ppODE(t.right) + "}")
    case ODESystem(ode, f)      => assert(false, "ODESystem does not occur recursively"); ??? //{" + ppODE(ode) + op(program).opcode + pp(f) + "}"
  }

  /** Formatting the atomic statement s */
  private def statement(s: String): String = if (statementSemicolon) s + ";" else s

}

/**
 * Precedence-based: KeYmaera X Pretty Printer formats differential dynamic logic expressions with compact brackets
 * in KeYmaera X notation according to the concrete syntax of differential dynamic logic
 * with explicit statement end ``;`` operator.
 * @author aplatzer
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
 * @author aplatzer
 */
object FullPrettyPrinter extends KeYmaeraXPrinter {
  override def apply(expr: Expression): String = stringify(expr)
}