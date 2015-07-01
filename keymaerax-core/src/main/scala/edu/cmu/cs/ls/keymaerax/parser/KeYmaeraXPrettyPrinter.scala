/**
 * Differential Dynamic Logic pretty printer in concrete KeYmaera X notation.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.parser

import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.core._

/**
 * KeYmaera X Pretty Printer formats differential dynamic logic expressions
 * in KeYmaera X notation according to the concrete syntax of differential dynamic logic
 * with explicit statement end ``;`` operator.
 * @author aplatzer
 * @todo Augment with ensuring postconditions that check correct reparse non-recursively.
 * @see doc/dL-grammar.md
 */
object KeYmaeraXPrettyPrinter extends (Expression => String) {
  import OpSpec.op
  import OpSpec.statementSemicolon

  private val checkPrettyPrinter = true

  /** Pretty-print term to a string */
  def apply(expr: Expression): String = stringify(expr) ensuring(
    r => !checkPrettyPrinter || KeYmaeraXParser(r) == expr, "Parse of print is identity.\nExpression: " + expr + "\nPrinted:   " + stringify(expr) + "\nReparsed:   " + KeYmaeraXParser(stringify(expr))
    )

  /** Pretty-print term to a string without contract checking. */
  private[parser] def stringify(expr: Expression) = expr match {
    case t: Term => pp(t)
    case f: Formula => pp(f)
    case p: Program => pp(p)
  }

  /**
   * Whether parentheses around ``t.child`` can be skipped because they are implied.
   */
  private def skipParens(t: UnaryComposite): Boolean = op(t.child) <= op(t)
  private def skipParens(t: Quantified): Boolean = op(t.child) <= op(t)
  private def skipParens(t: Modal): Boolean = op(t.child) <= op(t)

  /**
   * Whether parentheses around ``t.left`` can be skipped because they are implied.
   * @note Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
   */
  private def skipParensLeft(t: BinaryComposite): Boolean =
    op(t.left) < op(t) || op(t.left) <= op(t) && op(t).assoc == LeftAssociative && op(t.left).assoc == LeftAssociative

  /**
   * Whether parentheses around ``t.right`` can be skipped because they are implied.
   * @note Based on (seemingly redundant) inequality comparisons since equality incompatible with comparison ==
   */
  private def skipParensRight(t: BinaryComposite): Boolean =
    op(t.right) < op(t) || op(t.right) <= op(t) && op(t).assoc == RightAssociative && op(t.right).assoc == RightAssociative

  private def pp(term: Term): String = term match {
    case DotTerm|Anything|Nothing=> op(term).opcode
    case x: Variable            => x.asString
    case DifferentialSymbol(x)  => pp(x) + op(term).opcode
    case Differential(t)        => "(" + pp(t) + ")" + op(term).opcode
    case Number(n)              => n.toString()
    case FuncOf(f, c)           => f.asString + "(" + pp(c) + ")"
    case Pair(l, r)             => "(" + pp(l) + op(term).opcode + pp(r) + ")"
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
    case f: ComparisonFormula   => pp(f.left) + op(formula).opcode + pp(f.right)
    case DifferentialFormula(g) => "(" + pp(g) + ")" + op(formula).opcode
    case f: Quantified          => op(formula).opcode + " " + f.vars.map(pp).mkString(",") + /**/"."/**/ + (if (skipParens(f)) pp(f.child) else "(" + pp(f.child) + ")")
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
    case ODESystem(ode, f)      => "{" + pp(ode) + op(program).opcode + pp(f) + "}"
    case t: Loop                => (if (skipParens(t)) pp(t.child) else "{" + pp(t.child) + "}") + op(program).opcode
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

  private def pp(program: DifferentialProgram): String = program match {
    case a: DifferentialProgramConst => a.asString
    case AtomicODE(xp, e)       => pp(xp) + op(program).opcode + pp(e)
    case t: DifferentialProduct =>
      (if (skipParensLeft(t)) pp(t.left) else "{" + pp(t.left) + "}") +
        op(t).opcode +
        (if (skipParensRight(t)) pp(t.right) else "{" + pp(t.right) + "}")
  }

  /** Formatting the atomic statement s */
  private def statement(s: String): String = if (statementSemicolon) s + ";" else s

}
