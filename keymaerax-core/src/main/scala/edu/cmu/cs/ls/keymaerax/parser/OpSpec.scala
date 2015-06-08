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
      //@note could replace by reflection getField("s" + expr.getClass.getSimpleName)
      //@todo could add a contract ensuring that constructor applied to expressions's children indeed produces expr.
    // terms
    case DotTerm         => sDotTerm
    case Nothing         => sNothing
    case Anything        => sAnything
    case t: Variable     => sVariable
    case t: Number       => sNumber
    case t: FuncOf       => sFuncOf
    case t: DifferentialSymbol => sDifferentialSymbol
    case t: Pair         => sPair
    case t: Differential => sDifferential
    case t: Neg          => sNeg
    case t: Power        => sPower
    case t: Times        => sTimes
    case t: Divide       => sDivide
    case t: Plus         => sPlus
    case t: Minus        => sMinus

    // formulas
    case DotFormula      => sDotFormula
    case True            => sTrue
    case False           => sFalse
    case f: PredOf       => sPredOf
    case f: PredicationalOf => sPredicationalOf
    case f: DifferentialFormula => sDifferentialFormula
    case f: Equal        => sEqual
    case f: NotEqual     => sNotEqual
    case f: GreaterEqual => sGreaterEqual
    case f: Greater      => sGreater
    case f: LessEqual    => sLessEqual
    case f: Less         => sLess
    case f: Forall       => sForall
    case f: Exists       => sExists
    case f: Box          => sBox
    case f: Diamond      => sDiamond
    case f: Not          => sNot
    case f: And          => sAnd
    case f: Or           => sOr
    case f: Imply        => sImply
    case f: Equiv        => sEquiv

    // programs
    case p: ProgramConst => sProgramConst
    case p: DifferentialProgramConst => sDifferentialProgramConst
    case p: Assign       => sAssign
    case p: DiffAssign   => sDiffAssign
    case p: AssignAny    => sAssignAny
    case p: Test         => sTest
    case p: ODESystem    => sODESystem
    case p: AtomicODE    => sAtomicODE
    case p: DifferentialProduct => sDifferentialProduct
    case p: Loop         => sLoop
    case p: Compose      => sCompose
    case p: Choice       => sChoice
  }

  /** The operator notation of the top-level operator of expr with opcode, precedence and associativity  */
  private[parser] def op(tok: Terminal): OpSpec = {
    tok.img match {
      //@note could almost(!) replace by reflection to search through all OpSpec and check their images.
      // terms
      case sDotTerm.opcode => sDotTerm
      //case sNothing.opcode => sNothing
      case sAnything.opcode => sAnything
      //case t: Variable => sVariable
      //case t: Number => sNumber
      //case t: FuncOf => sFuncOf
      case sDifferential.opcode => sDifferentialSymbol /*|| sDifferential || sDifferentialFormula*/
      //case t: Pair => sPair
      case sMinus.opcode => sNeg /*|| sMinus*/
      case sPower.opcode => sPower
      case sTimes.opcode => sTimes /*|| sLoop*/
      case sDivide.opcode => sDivide
      case sPlus.opcode => sPlus

      // formulas
      case sDotFormula.opcode => sDotFormula
      case sTrue.opcode => sTrue
      case sFalse.opcode => sFalse
      //case f: PredOf => sPredOf
      //case f: PredicationalOf => sPredicationalOf
      //case f: DifferentialFormula => sDifferentialFormula
      case sEqual.opcode => sEqual
      case sNotEqual.opcode => sNotEqual
      case sGreaterEqual.opcode => sGreaterEqual
      case sGreater.opcode => sGreater
      case sLessEqual.opcode => sLessEqual
      case sLess.opcode => sLess
      case sForall.opcode => sForall
      case sExists.opcode => sExists
//      case f: Box => sBox
//      case f: Diamond => sDiamond
      case sNot.opcode => sNot
      case sAnd.opcode => sAnd
      case sOr.opcode => sOr
      case sImply.opcode => sImply
      case sEquiv.opcode => sEquiv

      // programs
      //case p: ProgramConst => sProgramConst
      //case p: DifferentialProgramConst => sDifferentialProgramConst
//      case p: Assign => sAssign
//      case p: DiffAssign => sDiffAssign
//      case p: AssignAny => sAssignAny
      case sTest.opcode => sTest
//      case p: ODESystem => sODESystem
//      case p: AtomicODE => sAtomicODE
//      case p: DifferentialProduct => sDifferentialProduct
//      case sLoop.opcode => sLoop
      case sCompose.opcode => sCompose
      case sChoice.opcode => sChoice
    }
  } ensuring(r => r.opcode == tok.img, "OpSpec's opcode coincides with expected token " + tok)


  // terms
  val sDotTerm      = UnitOpSpec ("•",     0, DotTerm)
  val sNothing      = UnitOpSpec ("",      0, Nothing)
  val sAnything     = UnitOpSpec ("?",     0, Anything)
  val sVariable     = UnitOpSpec (none,    0, name => Variable(name, None, Real))
  val sNumber       = UnitOpSpec (none,    0, number => Number(BigDecimal(number)))
  val sFuncOf       = UnaryOpSpec[Term](none,    0, PrefixFormat, (name:String, e:Term) => FuncOf(Function(name, None, Real, Real), e))
  val sDifferentialSymbol = UnaryOpSpec("'", 0, PostfixFormat, (v:Term) => DifferentialSymbol(v.asInstanceOf[Variable]))
  def sPair         = ??? // OpNotation(",",     4, RightAssociative)
  val sDifferential = UnaryOpSpec("'",    10, PostfixFormat, Differential.apply _)
  val sNeg          = UnaryOpSpec("-",    11, PrefixFormat, Neg.apply _)
  val sPower        = BinaryOpSpec("^",   20, RightAssociative, Power.apply _)
  val sTimes        = BinaryOpSpec("*",    40, LeftAssociative, Times.apply _)
  val sDivide       = BinaryOpSpec("/",    40, LeftAssociative, Divide.apply _)
  val sPlus         = BinaryOpSpec("+",    50, LeftAssociative, Plus.apply _)
  val sMinus        = BinaryOpSpec("-",    50, LeftAssociative, Minus.apply _)

  // formulas
  val sDotFormula      = UnitOpSpec("_",     0, DotFormula)
  val sTrue            = UnitOpSpec("true",  0, True)
  val sFalse           = UnitOpSpec("false", 0, False)
  val sPredOf       = UnaryOpSpec(none,    0, PrefixFormat, (name, e:Expression) => PredOf(Function(name, None, Real, Bool), e.asInstanceOf[Term]))
  val sPredicationalOf = UnaryOpSpec(none,    0, PrefixFormat, (name, e:Formula) => PredicationalOf(Function(name, None, Bool, Bool), e.asInstanceOf[Formula]))
  val sDifferentialFormula = UnaryOpSpec("'", 80, PostfixFormat, DifferentialFormula.apply _)
  val sEqual        = lBinaryOpSpec("=",    90, AtomicBinaryFormat, Equal.apply _)
  val sNotEqual     = lBinaryOpSpec("!=",   90, AtomicBinaryFormat, NotEqual.apply _)
  val sGreaterEqual = lBinaryOpSpec(">=",   90, AtomicBinaryFormat, GreaterEqual.apply _)
  val sGreater      = lBinaryOpSpec(">",    90, AtomicBinaryFormat, Greater.apply _)
  val sLessEqual    = lBinaryOpSpec("<=",   90, AtomicBinaryFormat, LessEqual.apply _)
  val sLess         = lBinaryOpSpec("<",    90, AtomicBinaryFormat, Less.apply _ )
  val sForall       = BinaryOpSpec("\\forall",96, MixedBinary, (x:Expression, f:Expression) => Forall(Seq(x.asInstanceOf[Variable]), f.asInstanceOf[Formula]))
  val sExists       = BinaryOpSpec("\\exists",97, MixedBinary, (x:Expression, f:Expression) => Exists(Seq(x.asInstanceOf[Variable]), f.asInstanceOf[Formula]))
  val sBox          = BinaryOpSpec("[]",   98, MixedBinary, (_, a:Expression, f:Expression) => Box(a.asInstanceOf[Program], f.asInstanceOf[Formula]))
  val sDiamond      = BinaryOpSpec("<>",   99, MixedBinary, (_, a:Expression, f:Expression) => Diamond(a.asInstanceOf[Program], f.asInstanceOf[Formula]))
  val sNot          = UnaryOpSpec("!",   100, PrefixFormat, Not.apply _)
  val sAnd          = BinaryOpSpec("&",   110, LeftAssociative, And.apply _)
  val sOr           = BinaryOpSpec("|",   120, LeftAssociative, Or.apply _)
  val sImply        = BinaryOpSpec("->",  130, RightAssociative, Imply.apply _)
  val sEquiv        = BinaryOpSpec("<->", 130, NonAssociative, Equiv. apply _)

  // programs
  val sProgramConst = UnitOpSpec(none,    0, name => ProgramConst(name))
  val sDifferentialProgramConst = UnitOpSpec(none,  0, name => DifferentialProgramConst(name))
  val sAssign       = lBinaryOpSpec[Program](":=",  200, AtomicBinaryFormat, (x:Term, e:Term) => Assign(x.asInstanceOf[Variable], e.asInstanceOf[Term]))
  val sDiffAssign   = lBinaryOpSpec[Program](":=",  200, AtomicBinaryFormat, (xp:Term, e:Term) => DiffAssign(xp.asInstanceOf[DifferentialSymbol], e.asInstanceOf[Term]))
  val sAssignAny    = lUnaryOpSpecT[Program](":= *", 200, PrefixFormat, (x:Term) => AssignAny(x.asInstanceOf[Variable]))
  val sTest         = lUnaryOpSpecF[Program]("?",   200, PrefixFormat, (f:Formula) => Test(f.asInstanceOf[Formula]))
  val sODESystem    = BinaryOpSpec[Expression]("&",   200, NonAssociative, (_:String, ode:Expression, h:Expression) => ODESystem(ode.asInstanceOf[DifferentialProgram], h.asInstanceOf[Formula]))
  val sAtomicODE    = BinaryOpSpec[Program]("=",   200, AtomicBinaryFormat, (_:String, xp:Expression, e:Expression) => AtomicODE(xp.asInstanceOf[DifferentialSymbol], e.asInstanceOf[Term]))
  val sDifferentialProduct = BinaryOpSpec(",", 210, RightAssociative, DifferentialProduct.apply _)
  val sLoop         = UnaryOpSpec("*",   220, PostfixFormat, Loop.apply _)
  val sCompose      = BinaryOpSpec(";",   230, RightAssociative, Compose.apply _) //@todo compatibility mode for parser
  //valp: Compose     => OpNotation("",    230, RightAssociative)
  val sChoice       = BinaryOpSpec("++",  240, LeftAssociative, Choice.apply _)

}

