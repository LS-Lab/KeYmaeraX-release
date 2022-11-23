/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Differential Dynamic Logic pretty printer in concrete KeYmaera X notation.
 * @author Andre Platzer
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 * @note Code Review 2016-08-02
 */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.core.Number

import scala.math.Ordered

/** Operator associativity notational specification */
sealed trait OpNotation
/** Notational specification for nullary operators of arity 0 */
trait NullaryNotation extends OpNotation
/** Notational specification for unary operators of arity 1 */
trait UnaryNotation extends OpNotation
/** Notational specification for binary operators of arity 2 */
trait BinaryNotation extends OpNotation
/** Notational specification for ternary operators of arity 3 */
trait TernaryNotation extends OpNotation

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
/** Non-associative infix operators of arity 2, i.e. explicit parentheses ``a<->(b<->c)`` */
object NonAssociative extends BinaryNotation
/** Mixed binary operators of arity 2 */
object MixedBinary extends BinaryNotation

/** Atomic operators of arity 0 within syntactic category with 2 arguments from lower category */
object AtomicBinaryFormat extends BinaryNotation

/** Ternary operators with a terminal before each operand, like if P then a else b */
object TernaryPrefixFormat extends TernaryNotation

/**
 * Operator notation specification with precedence and associativity.
 * @author Andre Platzer
 * @todo Could add spacing weight information to determine how much spacing is added around an operator.
 *       Alternatively, spacing weight can be inferred from the prec numerics and how far they are apart.
 */
trait OpSpec extends Ordered[OpSpec] {
  /** opcode operator code used for string representation of this operator. */
  final def opcode: String = op.img
  /** Token for the operator in lexing and parsing */
  def op: Terminal
  /** prec unique precedence where smaller numbers indicate stronger binding. */
  def prec: Int
  /** notational associativity specification. */
  def assoc: OpNotation

  /** Compare this operator specification to another one such that ``this<other`` says that ``this`` binds stronger than ``other``. */
  def compare(other: OpSpec): Int = {
    prec - other.prec
  } /*ensures(r => r!=0 || this==other, "precedence assumed unique " + this + " compared to " + other)*/
  //@note violates this ensures clause since two different operators can have same precedence.
}

/** Nullary operator notation specification with a constructor. */
case class UnitOpSpec(op: Terminal, prec: Int,
                               const: String => Expression) extends OpSpec {
  final def assoc: OpNotation = AtomicFormat
}

object UnitOpSpec {
  def apply(op: Terminal, prec: Int,
             const: Expression) =
    new UnitOpSpec(op, prec, s => {assert(s == op.img); const})
}

/** Unary operator notation specification with a constructor and expected argument kind. */
case class UnaryOpSpec[T<:Expression](op: Terminal, prec: Int, assoc: UnaryNotation, kind: Kind,
                                const: (String, T) => T) extends OpSpec

object UnaryOpSpec {
  def apply[T<:Expression](op: Terminal, prec: Int, assoc: UnaryNotation, kind: Kind,
            const: T => T) =
    new UnaryOpSpec[T](op, prec, assoc, kind, (s, e) => {assert(s == op.img); const(e)})

  // mixed converters

  def lUnaryOpSpecT[T<:Expression](op: Terminal, prec: Int, assoc: UnaryNotation, kind: Kind,
                           const: (Term) => T) =
    new UnaryOpSpec(op, prec, assoc, kind, (s, e:T) => {assert(s == op.img); const(e.asInstanceOf[Term])})

  def lUnaryOpSpecF[T<:Expression](op: Terminal, prec: Int, assoc: UnaryNotation, kind: Kind,
                           const: (Formula) => T) =
    new UnaryOpSpec(op, prec, assoc, kind, (s, e:T) => {assert(s == op.img); const(e.asInstanceOf[Formula])})
}

/** Binary operator notation specification with a constructor and expected argument kinds. */
case class BinaryOpSpec[T<:Expression](op: Terminal, prec: Int, assoc: BinaryNotation, kind: (Kind,Kind),
                              const: (String, T, T) => T) extends OpSpec

object BinaryOpSpec {
  def apply[T<:Expression](op: Terminal, prec: Int, assoc: BinaryNotation, kind: (Kind,Kind),
            const: (T, T) => T) =
    new BinaryOpSpec[T](op, prec, assoc, kind, (s, e1, e2) => {assert(s == op.img); const(e1,e2)})

  // mixed converters

  def lBinaryOpSpec[T<:Expression](op: Terminal, prec: Int, assoc: BinaryNotation, kind: (Kind,Kind),
                           const: (Term, Term) => T) =
    new BinaryOpSpec(op, prec, assoc, kind, (s, e1:T, e2:T) => {assert(s == op.img); const(e1.asInstanceOf[Term],e2.asInstanceOf[Term])})
}

/** Ternary operator notation specification with one terminal per operand, with constructor and expected argument kinds. */
case class TernaryOpSpec[T<:Expression](op: Terminal, op2:Terminal, op3:Terminal, prec: Int, assoc: TernaryNotation, kind: (Kind,Kind,Kind),
                                       const: (String, T, T,T) => T) extends OpSpec

object TernaryOpSpec {
  def apply[T<:Expression](op: Terminal, op2:Terminal, op3:Terminal, prec: Int, assoc: TernaryNotation, kind: (Kind,Kind,Kind),
                           const: (T, T, T) => T) =
    new TernaryOpSpec[T](op, op2, op3, prec, assoc, kind, (s, e1, e2, e3) => {assert(s == op.img); const(e1,e2,e3)})
}


/**
 * Differential Dynamic Logic's concrete syntax: operator notation specifications.
 * @note Subtleties:
 *       sPower right associative to ensure `x^2^3` == `x^(2^3)` instead of `(x^2)^3`.
 *       sPower < sNeg to ensure `-x^2` == `-(x^2)` instead of `(-x)^2`.
 *       NUMBER lexer does not contain - sign to enable `x-5` to be parsed. Parser will make up for this, respecting binary versus unary operators.
 *       sEquiv nonassociative to ensure that `p()<->q()<->r()` does not parse since binding unclear.
 *       sAnd and sOr are right-associative to simplify stable position ordering during sequent decomposition.
 * @author Andre Platzer
 */
object OpSpec {
  /** Whether to terminate atomic statements with a semicolon instead of separating sequential compositions by a semicolon. */
  val statementSemicolon = true

  /** Whether to accept negative numbers as negative numbers as opposed to unary negation applied to a number. */
  val negativeNumber = false //@note parses -1 to (-1), but also -2^4 to (-2)^4 when true!

  /** `true` has unary negation `-` bind weakly like binary subtraction.
   * `false` has unary negation `-` bind strong just shy of power `^`. */
  val weakNeg: Boolean = true

  /** no notation */
  private val none = PSEUDO

  import UnaryOpSpec.lUnaryOpSpecF
  import UnaryOpSpec.lUnaryOpSpecT
  import BinaryOpSpec.lBinaryOpSpec

  /** Function(name,index,domain,sort) is created. */
  private[parser] def func(name: String, index: Option[Int] = None, domain: Sort, sort: Sort): Function = Function(name, index, domain, sort)

  /** The sort and domain of an interpreted function or None if uninterpreted */
  private[parser] def interpretedFuncSortDomain(name: String): Option[(Sort, Sort)] =
    InterpretedSymbols.preshipped.asNamedSymbols.find(n => n.name == name && n.index.isEmpty) match {
      case Some(f: Function) => Some(f.sort -> f.domain)
      case _ => None
    }

  // operator notation specifications

  // terms
  private val unterm = TermKind
  private val binterm = (TermKind,TermKind)
  val sDotTerm      = UnitOpSpec (none,     0, _ => DotTerm())
  val sNothing      = UnitOpSpec (NOTHING,  0, Nothing)
  val sVariable     = UnitOpSpec (none,     0, name => Variable(name, None, Real))
  val sNumber       = UnitOpSpec (none,     0, number => Number(BigDecimal(number)))
  val sUnitFunctional= UnitOpSpec(none,     0, name => UnitFunctional(name,AnyArg,Real))
  val sFuncOf       = UnaryOpSpec[Term](none,       0, PrefixFormat, unterm, (name:String, e:Term) => FuncOf(func(name, None, e.sort, Real), e))
  val sDifferentialSymbol = UnaryOpSpec[Term](PRIME,0, PostfixFormat, unterm, (v:Term) => DifferentialSymbol(v.asInstanceOf[Variable]))
  val sDifferential = UnaryOpSpec[Term] (PRIME,     5, PostfixFormat, unterm, Differential.apply _)
  val sPower        = BinaryOpSpec[Term](POWER,    20, RightAssociative/*!*/, binterm, Power.apply _)
  val sTimes        = BinaryOpSpec[Term](STAR,     40, LeftAssociative, binterm, Times.apply _)
  val sDivide       = BinaryOpSpec[Term](SLASH,    40, LeftAssociative/*!*/, binterm, Divide.apply _)
  val sNeg          = UnaryOpSpec[Term] (MINUS,    59/*!*/, PrefixFormat, unterm, Neg.apply _)    // -x^2 == -(x^2) != (-x)^2
  val sPlus         = BinaryOpSpec[Term](PLUS,     60, LeftAssociative, binterm, Plus.apply _)
  val sMinus        = BinaryOpSpec[Term](MINUS,    60, LeftAssociative/*!*/, binterm, Minus.apply _)
  val sPair         = BinaryOpSpec[Term](COMMA,   444, RightAssociative, binterm, Pair.apply _)

  // formulas
  private val unfml = (FormulaKind)
  private val binfml = (FormulaKind,FormulaKind)
  private val untermfml = unterm
  private val bintermfml = binterm
  private val quantfml = (TermKind/*Variable*/,FormulaKind)
  private val modalfml = (ProgramKind,FormulaKind)
  val sDotFormula   = UnitOpSpec(PLACE,                 0, DotFormula)
  val sTrue         = UnitOpSpec(TRUE,                  0, True)
  val sFalse        = UnitOpSpec(FALSE,                 0, False)
  //@todo resolve ambiguous reference: (name, e:Expression) should be (name, e:Term)
  val sPredOf       = UnaryOpSpec(none,                 0, PrefixFormat, untermfml, (name, e:Expression) => PredOf(func(name, None, e.sort, Bool), e.asInstanceOf[Term]))
  val sPredicationalOf = UnaryOpSpec(none,              0, PrefixFormat, unfml, (name, e:Formula) => PredicationalOf(func(name, None, e.sort, Bool), e.asInstanceOf[Formula]))
  val sUnitPredicational= UnitOpSpec(none,              0, name => UnitPredicational(name,AnyArg))
  val sDifferentialFormula = UnaryOpSpec[Formula](PRIME,80, PostfixFormat, unfml, DifferentialFormula.apply _)
  val sEqual        = lBinaryOpSpec(EQ,                90, AtomicBinaryFormat, bintermfml, Equal.apply _)
  assert(sEqual>sMinus, "formulas bind weaker than their constituent terms")
  val sNotEqual     = lBinaryOpSpec(NOTEQ,             90, AtomicBinaryFormat, bintermfml, NotEqual.apply _)
  val sGreaterEqual = lBinaryOpSpec(GREATEREQ,         90, AtomicBinaryFormat, bintermfml, GreaterEqual.apply _)
  val sGreater      = lBinaryOpSpec(RDIA,              90, AtomicBinaryFormat, bintermfml, Greater.apply _)
  val sLessEqual    = lBinaryOpSpec(LESSEQ,            90, AtomicBinaryFormat, bintermfml, LessEqual.apply _)
  val sLess         = lBinaryOpSpec(LDIA,              90, AtomicBinaryFormat, bintermfml, Less.apply _ )
  val sForall       = BinaryOpSpec[Expression](FORALL, 95, MixedBinary, quantfml, (x:Expression, f:Expression) => Forall(Seq(x.asInstanceOf[Variable]), f.asInstanceOf[Formula]))
  val sExists       = BinaryOpSpec[Expression](EXISTS, 95, MixedBinary, quantfml, (x:Expression, f:Expression) => Exists(Seq(x.asInstanceOf[Variable]), f.asInstanceOf[Formula]))
  val sBox          = BinaryOpSpec[Expression](PSEUDO, 95, MixedBinary, modalfml, (_:String, a:Expression, f:Expression) => Box(a.asInstanceOf[Program], f.asInstanceOf[Formula]))
  val sDiamond      = BinaryOpSpec[Expression](PSEUDO, 95, MixedBinary, modalfml, (_:String, a:Expression, f:Expression) => Diamond(a.asInstanceOf[Program], f.asInstanceOf[Formula]))
  val sNot          = UnaryOpSpec[Formula] (NOT,       99, PrefixFormat, unfml, Not.apply _)
  val sAnd          = BinaryOpSpec[Formula](AMP,      110, RightAssociative, binfml, And.apply _)
  val sOr           = BinaryOpSpec[Formula](OR,       120, RightAssociative, binfml, Or.apply _)
  val sImply        = BinaryOpSpec[Formula](IMPLY,    150, RightAssociative/*!*/, binfml, Imply.apply _)
  val sRevImply     = BinaryOpSpec[Formula](REVIMPLY, 150, LeftAssociative, binfml, (l:Formula, r:Formula) => Imply(r, l)) /* swaps arguments */
  val sEquiv        = BinaryOpSpec[Formula](EQUIV,    160, NonAssociative/*!*/, binfml, Equiv.apply _)

  // programs
  private val unprog = ProgramKind
  private val binprog = (ProgramKind,ProgramKind)
  private val bindiffprog = (DifferentialProgramKind,DifferentialProgramKind)
  private val bintermprog = binterm
  private val untermprog = unterm
  private val unfmlprog = (FormulaKind)
  private val diffprogfmlprog = (DifferentialProgramKind,FormulaKind)

  val sProgramConst = UnitOpSpec(none,    0, name => ProgramConst(name))
  val sSystemConst  = UnitOpSpec(none,    0, name => SystemConst(name))
  val sDifferentialProgramConst = UnitOpSpec(none,  0, name => DifferentialProgramConst(name))
  val sAssign       = lBinaryOpSpec[Program](ASSIGN,  200, AtomicBinaryFormat, bintermprog, (x:Term, e:Term) => Assign(x.asInstanceOf[Variable], e))
  assert(sAssign>sMinus, "atomic programs bind weaker than their constituent terms")
  //val sDiffAssign   = lBinaryOpSpec[Program](ASSIGN,  200, AtomicBinaryFormat, bintermprog, (xp:Term, e:Term) => DiffAssign(xp.asInstanceOf[DifferentialSymbol], e))
  val sAssignAny    = lUnaryOpSpecT[Program](ASSIGNANY,200, PostfixFormat, untermprog, (x:Term) => AssignAny(x.asInstanceOf[Variable]))
  val sTest         = lUnaryOpSpecF[Program](TEST,    200, PrefixFormat, unfmlprog, (f:Formula) => Test(f))
  val sIfThenElse   = TernaryOpSpec[Program](IF, LBRACE, ELSE, 260, TernaryPrefixFormat, (FormulaKind,ProgramKind,ProgramKind), (_:String, e1:Expression, e2:Expression, e3:Expression) => {
      val p = e1.asInstanceOf[Formula]
      e3 match {
        case Test(True) =>
          Choice(Compose(Test(p), e2.asInstanceOf[Program]),
            Test(Not(p)))
        case prg =>
          Choice(Compose(Test(p), e2.asInstanceOf[Program]),
            Compose(Test(Not(p)), prg.asInstanceOf[Program]))
      }
    })
  assert(sTest>sEquiv, "tests bind weaker than their constituent formulas")
  //@note same = operator so use sEqual.prec as precedence
  val sAtomicODE    = BinaryOpSpec[Program](EQ,        90, AtomicBinaryFormat, bintermprog, (_:String, xp:Expression, e:Expression) => AtomicODE(xp.asInstanceOf[DifferentialSymbol], e.asInstanceOf[Term]))
  val sDifferentialProduct = BinaryOpSpec(COMMA,       95, RightAssociative, bindiffprog, DifferentialProduct.apply _)
  val sODESystem    = BinaryOpSpec[Expression](AMP,   150, NonAssociative, diffprogfmlprog, (_:String, ode:Expression, h:Expression) => ODESystem(ode.asInstanceOf[DifferentialProgram], h.asInstanceOf[Formula]))
  val sLoop         = UnaryOpSpec[Program](STAR,      220, PostfixFormat, unprog, Loop.apply _)
  val sDLoop        = UnaryOpSpec[Program](DSTAR,     220, PostfixFormat, unprog, (p: Program) => Dual(Loop(Dual(p))))
  val sDual         = UnaryOpSpec[Program](DUAL,      220, PostfixFormat, unprog, Dual.apply _)
  val sCompose      = BinaryOpSpec[Program](SEMI,     230, RightAssociative, binprog, Compose.apply _) //@todo compatibility mode for parser
  val sChoice       = BinaryOpSpec[Program](CHOICE,   250, RightAssociative, binprog, Choice.apply _)
  val sDChoice      = BinaryOpSpec[Program](DCHOICE,  250, RightAssociative, binprog, (l: Program, r: Program) => Dual(Choice(Dual(l), Dual(r))))

  // pseudo tokens

  /** Parser needs a lookahead operator when actually already done, so don't dare constructing it */
  val sEOF          = UnitOpSpec  (EOF, Int.MaxValue, _ => throw new AssertionError("Cannot construct EOF"))
  /** Parser needs a lookahead operator when actually already done, so don't dare constructing it */
  val sNoneUnfinished = UnitOpSpec(PSEUDO, Int.MaxValue, _ => throw new AssertionError("Cannot construct NONE"))
  val sNone         = sNoneUnfinished
  /** Parser needs a lookahead operator when actually already done, so don't dare constructing it */
  val sNoneDone     = UnitOpSpec  (PSEUDO, Int.MinValue, _ => throw new AssertionError("Cannot construct NONE"))


  /** The operator notation of the top-level operator of ``expr`` with opcode, precedence and associativity  */
  def op(expr: Expression): OpSpec = expr match {
      //@note could replace by reflection getField("s" + expr.getClass.getSimpleName)
      //@todo could add a contract ensures that constructor applied to expressions's children indeed produces expr.
    // terms
    case _: DotTerm      => sDotTerm
    case Nothing         => sNothing
    case t: DifferentialSymbol => sDifferentialSymbol
    case t: Variable     => sVariable
    case t: Number       => sNumber
    case t: FuncOf       => sFuncOf
    case t: Pair         => sPair
    case t: Differential => sDifferential
    case t: Neg          => sNeg
    case t: Power        => sPower
    case t: Times        => sTimes
    case t: Divide       => sDivide
    case t: Plus         => sPlus
    case t: Minus        => sMinus
    case t: UnitFunctional => sUnitFunctional

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
    case f: UnitPredicational => sUnitPredicational

    // programs
    case p: ProgramConst => sProgramConst
    case p: DifferentialProgramConst => sDifferentialProgramConst
    case p: Assign       => sAssign
    //case p: DiffAssign   => sDiffAssign
    case p: AssignAny    => sAssignAny
    case p: Test         => sTest
    case p: ODESystem    => sODESystem
    case p: AtomicODE    => sAtomicODE
    case p: DifferentialProduct => sDifferentialProduct
    case p: Loop         => sLoop
    case p: Compose      => sCompose
    case p: Choice       => sChoice
    case p: Dual         => sDual
    case _: SystemConst  => sSystemConst

    case f: Function     => throw new AssertionError("No completed expressions of FunctionKind can be constructed")

  }

}

