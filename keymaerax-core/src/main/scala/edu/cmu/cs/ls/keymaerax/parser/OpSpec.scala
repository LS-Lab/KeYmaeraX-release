package edu.cmu.cs.ls.keymaerax.parser

import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.core.Number

import scala.math.Ordered

/** Operator associativity notational specification */
sealed trait OpNotation
trait NullaryNotation extends OpNotation
trait UnaryNotation extends OpNotation
trait BinaryNotation extends OpNotation

/** Atomic operators of arity 0 within syntactic category */
object AtomicFormat extends NullaryNotation
/** Unary prefix operators of arity 1 within syntactic category */
object PrefixFormat extends UnaryNotation
/** Unary postfix operators of arity 1 within syntactic category */
object PostfixFormat extends UnaryNotation
/** Left-associative infix operators of arity 2, i.e. ``x-y-z=(x-y)-z``*/
object LeftAssociative extends BinaryNotation
/** Right-associative infix operators of arity 2, i.e. ``x^y^z=x^(y^z)`` */
object RightAssociative extends BinaryNotation
/** Non-associative infix operators of arity 2, i.e. explicit parentheses */
object NonAssociative extends BinaryNotation
/** Mixed binary operators of arity 2 */
object MixedBinary extends BinaryNotation

/** Atomic operators of arity 0 within syntactic category with 2 arguments from lower category */
object AtomicBinaryFormat extends BinaryNotation

/**
 * Operator notation specification.
 * @todo Could add spacing weight information to determine how much spacing is added around an operator.
 */
trait OpSpec extends Ordered[OpSpec] {
  /** opcode operator code used for string representation */
  def opcode: String
  /** prec unique precedence where smaller numbers indicate stronger binding */
  def prec: Int
  /** notational associativity */
  def assoc: OpNotation

  def compare(other: OpSpec): Int = {
    prec - other.prec
  } /*ensuring(r => r!=0 || this==other, "precedence assumed unique " + this + " compared to " + other)*/
  //@note violates this: two different things can have same precedence.
}

case class UnitOpSpec(opcode: String, prec: Int,
                               const: String => Expression) extends OpSpec {
  def assoc = AtomicFormat
}

object UnitOpSpec {
  def apply(opcode: String, prec: Int,
             const: Expression) =
    new UnitOpSpec(opcode, prec, s => {assert(s == opcode); const})
}

case class UnaryOpSpec[T<:Expression](opcode: String, prec: Int, assoc: UnaryNotation,
                                const: (String, T) => T) extends OpSpec

object UnaryOpSpec {
  def apply[T<:Expression](opcode: String, prec: Int, assoc: UnaryNotation,
            const: T => T) =
    new UnaryOpSpec[T](opcode, prec, assoc, (s, e) => {assert(s == opcode); const(e)})

  // mixed converters

  def lUnaryOpSpecT[T<:Expression](opcode: String, prec: Int, assoc: UnaryNotation,
                           const: (Term) => T) =
    new UnaryOpSpec(opcode, prec, assoc, (s, e:T) => {assert(s == opcode); const(e.asInstanceOf[Term])})

  def lUnaryOpSpecF[T<:Expression](opcode: String, prec: Int, assoc: UnaryNotation,
                           const: (Formula) => T) =
    new UnaryOpSpec(opcode, prec, assoc, (s, e:T) => {assert(s == opcode); const(e.asInstanceOf[Formula])})
}

case class BinaryOpSpec[T<:Expression](opcode: String, prec: Int, assoc: BinaryNotation,
                              const: (String, T, T) => T) extends OpSpec

object BinaryOpSpec {
  def apply[T<:Expression](opcode: String, prec: Int, assoc: BinaryNotation,
            const: (T, T) => T) =
    new BinaryOpSpec[T](opcode, prec, assoc, (s, e1, e2) => {assert(s == opcode); const(e1,e2)})

  // mixed converters

  def lBinaryOpSpec[T<:Expression](opcode: String, prec: Int, assoc: BinaryNotation,
                           const: (Term, Term) => T) =
    new BinaryOpSpec(opcode, prec, assoc, (s, e1:T, e2:T) => {assert(s == opcode); const(e1.asInstanceOf[Term],e2.asInstanceOf[Term])})
}


/**
 * Differential Dynamic Logic operator notation specifications.
 * @author aplatzer
 */
object OpSpec {
  /** no notation */
  private val none = "???"

  import UnaryOpSpec.lUnaryOpSpecF
  import UnaryOpSpec.lUnaryOpSpecT
  import BinaryOpSpec.lBinaryOpSpec

  /** The operator notation of the top-level operator of expr with opcode, precedence and associativity  */
  def op(expr: Expression): OpSpec = expr match {
    // terms
    case DotTerm         => UnitOpSpec ("•",     0, DotTerm)
    case Nothing         => UnitOpSpec ("",      0, Nothing)
    case Anything        => UnitOpSpec ("?",     0, Anything)
    case t: Variable     => UnitOpSpec (none,    0, name => Variable(name, None, Real))
    case t: Number       => UnitOpSpec (none,    0, number => Number(BigDecimal(number)))
    case t: FuncOf       => UnaryOpSpec[Term](none,    0, PrefixFormat, (name:String, e:Term) => FuncOf(Function(name, None, Real, Real), e))
    case t: DifferentialSymbol => UnaryOpSpec("'", 0, PostfixFormat, (v:Term) => DifferentialSymbol(v.asInstanceOf[Variable]))
    //case t: Pair         => OpNotation(",",     4, RightAssociative)
    case t: Differential => UnaryOpSpec("'",    10, PostfixFormat, Differential.apply _)
    case t: Neg          => UnaryOpSpec("-",    11, PrefixFormat, Neg.apply _)
    case t: Power        => BinaryOpSpec("^",   20, RightAssociative, Power.apply _)
    case t: Times        => BinaryOpSpec("*",    40, LeftAssociative, Times.apply _)
    case t: Divide       => BinaryOpSpec("/",    40, LeftAssociative, Divide.apply _)
    case t: Plus         => BinaryOpSpec("+",    50, LeftAssociative, Plus.apply _)
    case t: Minus        => BinaryOpSpec("-",    50, LeftAssociative, Minus.apply _)

    // formulas
    case DotFormula      => UnitOpSpec("_",     0, DotFormula)
    case True            => UnitOpSpec("true",  0, True)
    case False           => UnitOpSpec("false", 0, False)
    case f: PredOf       => UnaryOpSpec(none,    0, PrefixFormat, (name, e:Expression) => PredOf(Function(name, None, Real, Bool), e.asInstanceOf[Term]))
    case f: PredicationalOf => UnaryOpSpec(none,    0, PrefixFormat, (name, e:Formula) => PredicationalOf(Function(name, None, Bool, Bool), e.asInstanceOf[Formula]))
    case f: DifferentialFormula => UnaryOpSpec("'", 80, PostfixFormat, DifferentialFormula.apply _)
    case f: Equal        => lBinaryOpSpec("=",    90, AtomicBinaryFormat, Equal.apply _)
    case f: NotEqual     => lBinaryOpSpec("!=",   90, AtomicBinaryFormat, NotEqual.apply _)
    case f: GreaterEqual => lBinaryOpSpec(">=",   90, AtomicBinaryFormat, GreaterEqual.apply _)
    case f: Greater      => lBinaryOpSpec(">",    90, AtomicBinaryFormat, Greater.apply _)
    case f: LessEqual    => lBinaryOpSpec("<=",   90, AtomicBinaryFormat, LessEqual.apply _)
    case f: Less         => lBinaryOpSpec("<",    90, AtomicBinaryFormat, Less.apply _ )
    case f: Forall       => BinaryOpSpec("\\forall",96, MixedBinary, (x:Expression, f:Expression) => Forall(Seq(x.asInstanceOf[Variable]), f.asInstanceOf[Formula]))
    case f: Exists       => BinaryOpSpec("\\exists",97, MixedBinary, (x:Expression, f:Expression) => Exists(Seq(x.asInstanceOf[Variable]), f.asInstanceOf[Formula]))
    case f: Box          => BinaryOpSpec("[]",   98, MixedBinary, (_, a:Expression, f:Expression) => Box(a.asInstanceOf[Program], f.asInstanceOf[Formula]))
    case f: Diamond      => BinaryOpSpec("<>",   99, MixedBinary, (_, a:Expression, f:Expression) => Diamond(a.asInstanceOf[Program], f.asInstanceOf[Formula]))
    case f: Not          => UnaryOpSpec("!",   100, PrefixFormat, Not.apply _)
    case f: And          => BinaryOpSpec("&",   110, LeftAssociative, And.apply _)
    case f: Or           => BinaryOpSpec("|",   120, LeftAssociative, Or.apply _)
    case f: Imply        => BinaryOpSpec("->",  130, RightAssociative, Imply.apply _)
    case f: Equiv        => BinaryOpSpec("<->", 130, NonAssociative, Equiv. apply _)

    // programs
    case p: ProgramConst => UnitOpSpec(none,    0, name => ProgramConst(name))
    case p: DifferentialProgramConst => UnitOpSpec(none,  0, name => DifferentialProgramConst(name))
    case p: Assign       => lBinaryOpSpec[Program](":=",  200, AtomicBinaryFormat, (x:Term, e:Term) => Assign(x.asInstanceOf[Variable], e.asInstanceOf[Term]))
    case p: DiffAssign   => lBinaryOpSpec[Program](":=",  200, AtomicBinaryFormat, (xp:Term, e:Term) => DiffAssign(xp.asInstanceOf[DifferentialSymbol], e.asInstanceOf[Term]))
    case p: AssignAny    => lUnaryOpSpecT[Program](":= *", 200, PrefixFormat, (x:Term) => AssignAny(x.asInstanceOf[Variable]))
    case p: Test         => lUnaryOpSpecF[Program]("?",   200, PrefixFormat, (f:Formula) => Test(f.asInstanceOf[Formula]))
    case p: ODESystem    => BinaryOpSpec[Expression]("&",   200, NonAssociative, (_:String, ode:Expression, h:Expression) => ODESystem(ode.asInstanceOf[DifferentialProgram], h.asInstanceOf[Formula]))
    case p: AtomicODE    => BinaryOpSpec[Program]("=",   200, AtomicBinaryFormat, (_:String, xp:Expression, e:Expression) => AtomicODE(xp.asInstanceOf[DifferentialSymbol], e.asInstanceOf[Term]))
    case p: DifferentialProduct => BinaryOpSpec(",", 210, RightAssociative, DifferentialProduct.apply _)
    case p: Loop         => UnaryOpSpec("*",   220, PostfixFormat, Loop.apply _)
    case p: Compose      => BinaryOpSpec(";",   230, RightAssociative, Compose.apply _) //@todo compatibility mode for parser
    //case p: Compose      => OpNotation("",    230, RightAssociative)
    case p: Choice       => BinaryOpSpec("++",  240, LeftAssociative, Choice.apply _)
  }

}
