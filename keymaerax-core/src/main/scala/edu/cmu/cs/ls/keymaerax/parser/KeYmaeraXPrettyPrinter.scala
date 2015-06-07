/**
 * Differential Dynamic Logic pretty printer in KeYmaera X notation.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._

import scala.math.Ordered

/** Operator associativity notational specification */
private abstract class OpAssociativity
/** Atomic operators of arity 0 within syntactic category */
private object AtomicFormat extends OpAssociativity
/** Unary operators of arity 1 within syntactic category */
private object UnaryFormat extends OpAssociativity
/** Left-associative infix operators of arity 2, i.e. ``x-y-z=(x-y)-z``*/
private object LeftAssociative extends OpAssociativity
/** Right-associative infix operators of arity 2, i.e. ``x^y^z=x^(y^z)`` */
private object RightAssociative extends OpAssociativity
/** Non-associative infix operators of arity 2, i.e. explicit parentheses */
private object NonAssociative extends OpAssociativity

/**
 * Operator notation specification.
 * @param opcode operator code used for string representation
 * @param prec unique precedence where smaller numbers indicate stronger binding
 * @param assoc associativity of this operator
 * @todo Could add spacing weight information to determine how much spacing is added around an operator.
 */
private case class OpNotation(opcode: String, prec: Int, assoc: OpAssociativity) extends Ordered[OpNotation] {
  def compare(other: OpNotation): Int = {
    prec - other.prec
  } /*ensuring(r => r!=0 || this==other, "precedence assumed unique " + this + " compared to " + other)*/
  //@note violates this: two different things can have same precedence.
}


/**
 * KeYmaera X Pretty Printer.
 * @author aplatzer
 * @todo Augment with ensuring postconditions that check correct reparse non-recursively.
 */
object KeYmaeraXPrettyPrinter extends (Expression => String) {

  /** Pretty-print term to a string */
  def apply(expr: Expression): String = expr match {
    case t: Term => pp(t)
    case f: Formula => pp(f)
    case p: Program => pp(p)
  }

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
    case x: Variable            => x.toString
    case DifferentialSymbol(x)  => pp(x) + op(term).opcode
    case Differential(t)        => "(" + pp(t) + ")" + op(term).opcode
    case Number(n)              => n.toString()
    case FuncOf(f, c)           => f.toString + "(" + pp(c) + ")"
    case Pair(l, r)             => "(" + pp(l) + op(term).opcode + pp(r) + ")"
    case t: UnaryCompositeTerm  => op(t).opcode + pp(t.child)
    case t: BinaryCompositeTerm =>
      (if (skipParensLeft(t)) pp(t.left) else "(" + pp(t.left) + ")") +
        op(t).opcode +
        (if (skipParensRight(t)) pp(t.right) else "(" + pp(t.right) + ")")
  }

  private def pp(formula: Formula): String = formula match {
    case True|False|DotFormula  => op(formula).opcode
    case PredOf(p, c)           => p.toString + "(" + pp(c) + ")"
    case PredicationalOf(p, c)  => p.toString + "{" + pp(c) + "}"
    case f: ComparisonFormula   => pp(f.left) + op(formula).opcode + pp(f.right)
    case DifferentialFormula(g) => "(" + pp(g) + ")" + op(formula).opcode
    case f: Quantified          => op(formula).opcode + f.vars.mkString(",") + /**/"."/**/ + pp(f.child)
    case f: Box                 => "[" + pp(f.program) + "]" + pp(f.child)
    case f: Diamond             => "<" + pp(f.program) + ">" + pp(f.child)
    case g: UnaryCompositeFormula=> op(g).opcode + pp(g.child)
    case t: BinaryCompositeFormula=>
      (if (skipParensLeft(t)) pp(t.left) else "(" + pp(t.left) + ")") +
        op(t).opcode +
        (if (skipParensRight(t)) pp(t.right) else "(" + pp(t.right) + ")")
  }

  private def pp(program: Program): String = program match {
    case ProgramConst(a)        => statement(a)
    case Assign(x, e)           => statement(pp(x) + op(program).opcode + pp(e))
    case AssignAny(x)           => statement(pp(x) + op(program).opcode)
    case DiffAssign(xp, e)      => statement(pp(xp) + op(program).opcode + pp(e))
    case Test(f)                => statement(op(program).opcode + pp(f))
    case p: DifferentialProgram => pp(p)
    case Loop(a)                => pp(a) + op(program).opcode
    //case p: UnaryCompositeProgram=> op(p).opcode + pp(p.child)
    case t: BinaryCompositeProgram=>
      (if (skipPrensLeft(t)) pp(t.left) else "{" + pp(t.left) + "}") +
        op(t).opcode +
        (if (skipParensRight(t)) pp(.right) else "{" + pp(t.right) + "}")
  }

  private def pp(program: DifferentialProgram): String = program match {
    case ODESystem(ode, f)      => "{" + pp(ode) + op(program).opcode + pp(f) + "}"
    case DifferentialProgramConst(a) => a.toString
    case AtomicODE(xp, e)       => pp(xp) + op(program).opcode + pp(e)
    case t: DifferentialProduct =>
      (if (skipParensLeft(t)) pp(t.left) else "{" + pp(t.left) + "}") +
        op(t).opcode +
        (if (skipParensRight(t)) pp(t.right) else "{" + pp(t.right) + "}")
  }

  /** Formatting the atomic statement s */
  private def statement(s: String): String = s + ";"

  /** The operator notation of the top-level operator of expr with opcode, precedence and associativity  */
  private def op(expr: Expression) = expr match {
    case DotTerm         => OpNotation("•",     0, AtomicFormat)
    case Nothing         => OpNotation("",      0, AtomicFormat)
    case Anything        => OpNotation("?",     0, AtomicFormat)
    case t: Variable     => OpNotation("???",   0, AtomicFormat)
    case t: Number       => OpNotation("???",   0, AtomicFormat)
    case t: FuncOf       => OpNotation("???",   0, AtomicFormat)
    case t: DifferentialSymbol => OpNotation("'", 0, AtomicFormat)
    case t: Differential => OpNotation("'",    10, UnaryFormat)
    case t: Neg          => OpNotation("-",    11, UnaryFormat)
    case t: Power        => OpNotation("^",    20, RightAssociative)
    case t: Times        => OpNotation("*",    30, LeftAssociative)
    case t: Divide       => OpNotation("/",    40, LeftAssociative)
    case t: Plus         => OpNotation("+",    50, LeftAssociative)
    case t: Minus        => OpNotation("-",    60, LeftAssociative)
    case t: Pair         => OpNotation(",",     2, RightAssociative)

    case DotFormula      => OpNotation("_",     0, AtomicFormat)
    case True            => OpNotation("true",  0, AtomicFormat)
    case False           => OpNotation("false", 0, AtomicFormat)
    case t: PredOf       => OpNotation("???",   0, AtomicFormat)
    case t: PredicationalOf => OpNotation("???",   0, AtomicFormat)
    case t: DifferentialFormula => OpNotation("'", 80, UnaryFormat)
    case f: Equal        => OpNotation("=",    90, NonAssociative)
    case f: NotEqual     => OpNotation("!=",   90, NonAssociative)
    case f: GreaterEqual => OpNotation(">=",   90, NonAssociative)
    case f: Greater      => OpNotation(">",    90, NonAssociative)
    case f: LessEqual    => OpNotation("<=",   90, NonAssociative)
    case f: Less         => OpNotation("<",    90, NonAssociative)
    case f: Forall       => OpNotation("\\forall",96, UnaryFormat)
    case f: Exists       => OpNotation("\\exists",97, UnaryFormat)
    case f: Box          => OpNotation("[]",   98, UnaryFormat)
    case f: Diamond      => OpNotation("<>",   99, UnaryFormat)
    case f: Not          => OpNotation("!",   100, UnaryFormat)
    case f: And          => OpNotation("&",   110, LeftAssociative)
    case f: Or           => OpNotation("|",   120, LeftAssociative)
    case f: Imply        => OpNotation("->",  130, RightAssociative)
    case f: Equiv        => OpNotation("<->", 130, NonAssociative)

    case t: ProgramConst => OpNotation("???",   0, AtomicFormat)
    case t: DifferentialProgramConst => OpNotation("???",   0, AtomicFormat)
    case p: Assign       => OpNotation(":=",  200, AtomicFormat)
    case p: DiffAssign   => OpNotation(":=",  200, AtomicFormat)
    case p: AssignAny    => OpNotation(":= *", 200, AtomicFormat)
    case p: Test         => OpNotation("?",   200, AtomicFormat)
    case p: ODESystem    => OpNotation("&",   200, NonAssociative)
    case p: AtomicODE    => OpNotation("=",   200, AtomicFormat)
    case p: DifferentialProduct => OpNotation(",", 210, RightAssociative)
    case p: Loop         => OpNotation("*",   220, UnaryFormat)
    case p: Compose      => OpNotation(";",    230, RightAssociative) //@todo compatibility mode for parser
    //case p: Compose      => OpNotation("",    230, RightAssociative)
    case p: Choice       => OpNotation("++",  240, LeftAssociative)
  }
}
