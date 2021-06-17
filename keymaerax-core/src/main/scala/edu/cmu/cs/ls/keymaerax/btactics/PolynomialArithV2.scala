package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms._
import edu.cmu.cs.ls.keymaerax.btactics.SimplifierV3._
import edu.cmu.cs.ls.keymaerax.btactics.AnonymousLemmas._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.infrastruct.{RenUSubst, SubstitutionHelper}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.btactics.PolynomialArithV2.{NonPolynomialArithmeticException, NonSupportedDivisorException, NonSupportedExponentException, NonSupportedOperationException}
import edu.cmu.cs.ls.keymaerax.tools.ext.RingsLibrary
import edu.cmu.cs.ls.keymaerax.btactics.macros._

import scala.collection.immutable._

/**
  * Polynomial Ring:
  *
  * - interface that describes [[Polynomial]]s and operations on them
  * - constructors for Polynomials from constant numbers, variables, and recursively from terms
  * */
trait PolynomialRing {

  /**
    * Interface to [[Polynomial]]s:
    * - a [[term]] that keeps track of how the polynomial was constructed
    * - a proof for the internal [[representation]] of the polynomial
    * - arithmetic
    * - test for zero
    * */
  trait Polynomial {
    val term: Term
    // proof of "term = some internal representation"
    def representation: ProvableSig
    // proof of "term = some pretty representation"
    def prettyRepresentation: ProvableSig
    // resetTerm.term = some internal representation
    def resetTerm : Polynomial
    // resetRepresentation(newRepresentation).representation = newRepresentation
    def resetRepresentation(newRepresentation: ProvableSig) : Polynomial
    // prettyTerm.term = rhsOf(prettyRepresentation)
    def prettyTerm : Polynomial

    // result.term = term + other.term
    def +(other: Polynomial) : Polynomial

    // result.term = term - other.term
    def -(other: Polynomial) : Polynomial

    // result.term = term * other.term
    def *(other: Polynomial) : Polynomial

    // result.term = -term
    def unary_- : Polynomial

    // result.term = term ^ n
    def ^(n: Int) : Polynomial

    // result.term = term ^ other.term if other.term normalizes to an integer constant
    def ^(other: Polynomial) : Polynomial

    // result.term = term / other.term if other.term normalizes to a nonzero constant
    def /(other: Polynomial) : Polynomial

    // Some(proof of "term = other.term") by equating coefficients
    def equate(other: Polynomial) : Option[ProvableSig]

    // partition monomials (where (num, denom, (x_i, p_i)_(i)) represents num/denom*(x_1^p^1 * ... * x_n^p_n)
    // partition(P) = (proof of "term = p1.term + p2.term", p1, p2)
    //   where p1's monomials satisfy P and p2's monomials satisfy !P
    def partition(P: (BigDecimal, BigDecimal, PowerProduct) => Boolean) : (Polynomial, Polynomial, ProvableSig)

    // approx(prec) = (proof of "term = p1.term + p2.term", p1, p2)
    //   where the coefficients p1 are rounded to (decimal) precision [[prec]]
    def approx(prec: Int) : (ProvableSig, Polynomial, Polynomial)

    // degree with respect to the variables for which "include" is true
    def degree(include: Term=>Boolean = _ => true) : Int

    // coefficient (numerator, denominator) of monomial (x_i, p_i)_(i) x_i^p_i:
    def coefficient(powerProduct: PowerProduct) : (BigDecimal, BigDecimal)

    // Some(proof of "term = 0") or None
    def zeroTest : Option[ProvableSig]

    // proof of "poly.term = horner form"
    def hornerForm(variableOrder: Option[List[Term]] = None) : ProvableSig

    // quotient and remainder:
    // divideAndRemainder(other) = ((pretty)quot, (pretty)rem, proof of "term = quot.term * other.term + rem.term")
    def divideAndRemainder(other: Polynomial, pretty: Boolean = true) : (Polynomial, Polynomial, ProvableSig)

    // variables of this polynomial
    def variables : Set[Term]
  }

  trait PowerProduct {
    def sparse : Seq[(Term, Int)]
    val degree : Int
  }
  def ofSparse(seq: Seq[(Term, Int)]) : PowerProduct
  def ofSparse(seq: (Term, Int)*) : PowerProduct

  // result.term = n
  def Const(n: BigDecimal) : Polynomial

  // result.term = num/denom
  def Const(num: BigDecimal, denom: BigDecimal) : Polynomial

  // result.term = t ^ n
  def Var(t: Term, n: Int) : Polynomial

  // result.term = t
  def Var(t: Term) : Polynomial

  // result.term = t
  def ofTerm(t: Term) : Polynomial = t match {
    case Plus(a, b)  => ofTerm(a) + ofTerm(b)
    case Minus(a, b) => ofTerm(a) - ofTerm(b)
    case Times(a, b) => ofTerm(a) * ofTerm(b)
    case Neg(a)      => -ofTerm(a)
    case Power(a, Number(i)) if i.isValidInt && i >= 0 => ofTerm(a) ^ i.toIntExact
    case Power(a, b) => ofTerm(a) ^ ofTerm(b)
    case Divide(a, b) => ofTerm(a) / ofTerm(b)
    case Number(n) => Const(n)
    case term: Term => Var(term)
  }

  // subterms that are interpreted as variables
  def symbols(t: Term) : Seq[Term] = t match {
    case Plus(a, b)  => symbols(a) ++ symbols(b)
    case Minus(a, b) => symbols(a) ++ symbols(b)
    case Times(a, b) => symbols(a) ++ symbols(b)
    case Neg(a)      => symbols(a)
    case Power(a, Number(i)) if i.isValidInt && i >= 0 => symbols(a)
    case Power(a, b) => symbols(a) ++ symbols(b)
    case Divide(a, b) => symbols(a) ++ symbols(b)
    case Number(n) => Seq()
    case term: Term => Seq(term)
  }

  implicit def ofInt(i: Int) : Polynomial = Const(BigDecimal(i))

  // Prove "t1 = t2" by equating coefficients
  def equate(t1: Term, t2: Term) : Option[ProvableSig]

  // Prove an equality by equating coefficients
  val equate : DependentPositionTactic

  // distributive normal form
  def normalize(term: Term) : ProvableSig

  // normalizeAt "term" rewrites polynomial term to distributive normal form
  // normalizeAt "t1 = t2" rewrites to "normalize(t1 - t2) = 0"
  val normalizeAt : DependentPositionTactic

  // ratForm(term) = (num, denom, proof of "term = num.term / denom.term")
  def ratForm(term: Term) : (Polynomial, Polynomial, ProvableSig)

}

/**
  * Polynomial Arithmetic.
  *
  * Computations are carried out fairly efficiently in a distributive representation.
  * Computations are certifying:
  *   - the internal data structures maintain a proof that the constructed term equals the distributive representation
  *
  * The main interface is that of a [[PolynomialRing]]
  *
  * @author Fabian Immler
  */
object PolynomialArithV2 extends TwoThreeTreePolynomialRing(
  MonomialOrders.variableConstantOrdering,
  MonomialOrders.grevlex(MonomialOrders.variableConstantOrdering)) {

  /** constructor for given variable and monomial orderings */
  def PolynomialRing(variableOrdering: Ordering[Term],
                     monomialOrdering: Ordering[IndexedSeq[(Term, Int)]]): PolynomialRing =
    TwoThreeTreePolynomialRing(variableOrdering, monomialOrdering)

  /** report operations not supported by polynomial arithmetic in computations */
  trait NonSupportedOperationException extends IllegalArgumentException
  final case class NonSupportedExponentException(message: String)
    extends IllegalArgumentException(message) with PolynomialArithV2.NonSupportedOperationException
  final case class NonSupportedDivisorException(message: String)
    extends IllegalArgumentException(message) with PolynomialArithV2.NonSupportedOperationException
  final case class NonPolynomialArithmeticException(message: String)
    extends IllegalArgumentException(message) with PolynomialArithV2.NonSupportedOperationException

  /** report operations not supported by polynomial arithmetic in tactics */
  final case class NonSupportedOperationInapplicability(cause: NonSupportedOperationException)
    extends TacticInapplicableFailure("Tactic inapplicable because of an operation that is not supported by polynomial arithmetic: " +
      cause.getMessage
      , cause)
  def reportBelleThrowables[R](block: => R) =
    try {
      block
    } catch {
      case nonSupportedOperationException: NonSupportedOperationException =>
        throw NonSupportedOperationInapplicability(nonSupportedOperationException)
    }

}

object MonomialOrders {
  val variableConstantOrdering: Ordering[Term] = Ordering.by{
    case BaseVariable(n, i, Real) => (0, n, i)
    case DifferentialSymbol(BaseVariable(n, i, Real)) => (0, n, i)
    case FuncOf(Function(n, i, Unit, Real, None), Nothing) => (1, n, i)
    case t => throw new IllegalArgumentException("variableConstantOrdering expects BaseVariable or FuncOf(_, Nothing) of sort Real, but got " + t)
  }


  /** reverse lexicographic order -- @note: strange legacy default */
  def revlex(variableOrdering: Ordering[Term]) : Ordering[IndexedSeq[(Term, Int)]] = new Ordering[IndexedSeq[(Term, Int)]] {
    override def compare(x: IndexedSeq[(Term, Int)], y: IndexedSeq[(Term, Int)]): Int = {
      val lx = x.length
      val ly = y.length
      def px(i: Int): Int = if (i < lx) x(i)._2 else 0
      def py(i: Int): Int = if (i < ly) y(i)._2 else 0
      def compareAt(i: Int, j: Int): Int = {
        val (lastPowerX, lastPowerY) =
          if (i < lx && j < ly) {
            variableOrdering.compare(x(i)._1, y(j)._1) match {
              case c if c < 0 => (px(i), 0)
              case c if c > 0 => (0, py(j))
              case c if c == 0 => (px(i), py(j))
            }
          } else if (i < lx) {
            (px(i), 0)
          } else if (j < ly) {
            (0, py(j))
          } else {
            (0, 0)
          }
        lastPowerX.compare(lastPowerY) match {
          case c if c == 0 => if (i < lx || j < ly) compareAt(i + 1, j + 1) else 0
          case c => c
        }
      }
      -compareAt(0, 0)
    }
  }

  /** Graded reverse lexicographic order */
  def grevlex(variableOrdering: Ordering[Term]) : Ordering[IndexedSeq[(Term, Int)]] = new Ordering[IndexedSeq[(Term, Int)]] {
    override def compare(x: IndexedSeq[(Term, Int)], y: IndexedSeq[(Term, Int)]): Int = {
      val lx = x.length
      val ly = y.length
      def px(i: Int): Int = if (i < lx) x(i)._2 else 0
      def py(i: Int): Int = if (i < ly) y(i)._2 else 0
      def compareAt(i: Int, j: Int): Int = {
        val (lastPowerX, lastPowerY) =
          if (i >= 0 && j >= 0) {
            variableOrdering.compare(x(i)._1, y(j)._1) match {
              case c if c < 0 => (0, py(j))
              case c if c > 0 => (px(i), 0)
              case c if c == 0 => (px(i), py(j))
            }
          } else if (i >= 0) {
            (px(i), 0)
          } else if (j >= 0) {
            (0, py(j))
          } else {
            (0, 0)
          }
        lastPowerX.compare(lastPowerY) match {
          case c if c == 0 => if (i >= 0 || j >= 0) compareAt(i - 1, j - 1) else 0
          case c => -c
        }
      }
      x.map(_._2).sum.compareTo(y.map(_._2).sum) match {
        case 0 => compareAt(lx - 1, ly - 1)
        case c => c
      }
    }
  }

}

object PolynomialArithV2Helpers {
  // TODO: move somewhere reasonable
  def constR(name: String) = FuncOf(Function(name, None, Unit, Real), Nothing)
  def anyR(name: String) = UnitFunctional(name, AnyArg, Real)

  // @note: exposing private methods, only for tests
  def usePrvAt(fact: ProvableSig, key: PosInExpr): DependentPositionTactic = useAt(fact, key)
  def usePrvFor(fact: ProvableSig, key: PosInExpr): ForwardPositionTactic = useFor(fact, key)

  def substAny(s: String, t: Term) = USubst(Seq(SubstitutionPair(anyR(s), t)))

  def anyArgify(prv: ProvableSig): ProvableSig = {
    require(prv.isProved)
    val us = USubst(StaticSemantics.signature(prv.conclusion).flatMap{
      case f@Function(n, None, Unit, Real, None) => Some(SubstitutionPair(FuncOf(f, Nothing), UnitFunctional(n, AnyArg, Real)))
      case _ => None
    }.toIndexedSeq)
    prv(us)
  }
  def anyArgify(ax: DerivedAxiomInfo): ProvableSig = anyArgify(ax.provable)

  lazy val equalReflex = anyArgify(Ax.equalReflexive.provable)
  val spat = "s_(||)".asTerm
  def equalReflex(t: Term) : ProvableSig = equalReflex(USubst(Seq(SubstitutionPair(spat, t))))

  def substOfInst(inst: Seq[(String, Term)]) = USubst(inst.map{case(a, b) => SubstitutionPair(anyR(a), b)})
  def useDirectly(prv: ProvableSig, inst: Seq[(String, Term)], assms: Seq[ProvableSig]) : ProvableSig = {
    val prv2 = prv(substOfInst(inst))
    impliesElim(prv2, assms)
  }
  def useDirectlyConst(prv: ProvableSig, inst: Seq[(String, Term)], assms: Seq[ProvableSig]) : ProvableSig = {
    val prv2 = prv(USubst(inst.map { case (a, b) => SubstitutionPair(constR(a), b) }))
    impliesElim(prv2, assms)
  }

  // G |- P->Q   G |- P
  // ---------
  // G |- Q
  def impliesElim(PQ: ProvableSig, P: ProvableSig) : ProvableSig = {
    require(PQ.isProved)
    require(P.isProved)
    require(PQ.conclusion.succ.length == 1)
    require(P.conclusion.succ.length == 1)
    val pq = PQ.conclusion.succ(0)
    val p = P.conclusion.succ(0)
    pq match {
      case Imply(pp, q) => ProvableSig.startProof(Sequent(PQ.conclusion.ante, IndexedSeq(q)))(CutRight(p, SuccPos(0)), 0)(PQ, 1)(P, 0)
      case _ => throw new IllegalArgumentException("Cannot impliesElim here")
    }
  }

  /**
    * PsQ: G |- (p1 & ... & pn) -> q
    * Ps: G |- p1, ... G |- pn
    * @return G |- q
    * */
  def impliesElim(PsQ: ProvableSig, Ps: Seq[ProvableSig]) : ProvableSig =
    if (Ps.length == 0) PsQ
    else {
      val conj = Ps.map(P => P.conclusion.succ(0)).reduceRight(And)
      val conjPrv = Ps.dropRight(1).foldLeft(ProvableSig.startProof(Sequent(PsQ.conclusion.ante, IndexedSeq(conj)))){(prv, P) =>
        prv(AndRight(SuccPos(0)), 0)(P, 0)
      }(Ps.last, 0)
      impliesElim(PsQ, conjPrv)
    }

  def byExact(assm: ProvableSig) = anon { (prv: ProvableSig, pos: SuccPosition) =>
    assert(prv.subgoals.length==1, "require one subgoal byExact")
    prv.apply(assm, 0)
  }

  def rhsOf(prv: ProvableSig) = prv.conclusion.succ(0).asInstanceOf[Equal].right
  def lhsOf(prv: ProvableSig) = prv.conclusion.succ(0).asInstanceOf[Equal].left

}

/**
* A polynomial is represented as a set of monomials stored in a 2-3 Tree, the ordering is lexicographic
* A monomial is represented as a coefficient and a power-product.
* A coefficient is represented as a pair of BigDecimals for num/denom.
* A power product is represented densely as a list of exponents
*
* All data-structures maintain a proof of
*  input term = representation of data structure as Term
*
* Representations of data structures (recursively applied on rhs):
*   - 3-Node (l, v1, m, v2, r) is "l + v1 + m + v2 + r"
*   - 2-Node (l, v, r) is "l + v + r"
*   - monomial (c, pp) is "c * pp"
*   - coefficient (num, denom) is "num / denom"
*   - power product [e1, ..., en] is "x1^e1 * ... * xn ^ en",
*     where instead of "x^0", we write "1" in order to avoid trouble with 0^0, i.e., nonzero-assumptions on x or the like
*
* All operations on the representations update the proofs accordingly.
*
*/
case class TwoThreeTreePolynomialRing(variableOrdering: Ordering[Term],
                                      monomialOrdering: Ordering[IndexedSeq[(Term, Int)]]) extends PolynomialRing {
  import PolynomialArithV2Helpers._
  val constL = constR("l_")
  val constR_ = constR("r_")
  val constCl = constR("cl_")
  val constCr = constR("cr_")
  val constC = constR("c_")


  val constLn = constR("ln_")
  val constLd = constR("ld_")
  val constRn = constR("rn_")
  val constRd = constR("rd_")
  lazy val coefficientTimesPrv = anyArgify(Ax.coefficientTimesPrv)
  lazy val coefficientPlusPrv = anyArgify(Ax.coefficientPlusPrv)
  lazy val coefficientNegPrv = anyArgify(Ax.coefficientNegPrv)

  lazy val coefficientBigDecimalPrv = anyArgify(Ax.coefficientBigDecimalPrv)

  /**
  * prv: lhs = rhs
  * lhs: input term (arbitrary, trace of construction)
  * rhs: Divide(Number(num), Number(denom))
  */
  case class Coefficient(num: BigDecimal, denom: BigDecimal,
                         prvO: Option[ProvableSig] = None) {
    val numN = Number(num)
    val denomN = Number(denom)
    // @note detour for "dependent" default argument
    lazy val defaultPrv = equalReflex(Divide(numN, denomN))
    val prv = prvO.getOrElse(defaultPrv)
    def forgetPrv = Coefficient(num, denom, Some(defaultPrv))
    def rhsString = if (num.compareTo(0) == 0) "0"
    else if (denom.compareTo(1) == 0) num.toString
    else num.toString + "/" + denom.toString

    assert(prv.subgoals.isEmpty)
    assert(prv.conclusion.ante.isEmpty)
    assert(prv.conclusion.succ.length==1)
    assert(prv.conclusion.succ(0) match {
      case Equal(lhs, Divide(Number(n), Number(d))) => n == num && d == denom
      case _ => false
    })
    val (eq, lhs, rhs) = prv.conclusion.succ(0) match { case eq @ Equal(lhs, rhs@Divide(n, d)) => (eq, lhs, rhs) }

    def unary_- : Coefficient = {
      val negPrv = ProvableSig.proveArithmetic(BigDecimalQETool, And(Equal(Neg(numN), Number(-num)), NotEqual(denomN, Number(0))))
      Coefficient(-num, denom, Some(useDirectly(coefficientNegPrv,
        Seq(
          ("x_", lhs),
          ("xn_", numN),
          ("xd_", denomN),
          ("nxn_", Number(-num))
        ),
        Seq(prv, negPrv)
      )))
    }

    def +(that: Coefficient) : Coefficient = {
      val numRes = BigDecimalQETool.eval(Plus(Times(Number(num), Number(that.denom)), Times(Number(that.num), Number(denom))))
      val denomRes = BigDecimalQETool.eval(Times(Number(denom), Number(that.denom)))
      val inst = Seq(
        ("ln_", numN),
          ("ld_", denomN),
          ("rn_", that.numN),
          ("rd_", that.denomN),
          ("l_", lhs),
          ("r_", that.lhs),
          ("pn_", Number(numRes)),
          ("pd_", Number(denomRes)))
      val numericPrv = ProvableSig.proveArithmetic(BigDecimalQETool,
        List(
          Equal(Plus(Times(numN, that.denomN), Times(that.numN, denomN)), Number(numRes)),
          Equal(Times(denomN, that.denomN), Number(denomRes)),
          NotEqual(denomN, Number(0)),
          NotEqual(that.denomN, Number(0)),
        ).reduceRight(And)
      )
      val prvRes = useDirectly(coefficientPlusPrv, inst, Seq(prv, that.prv, numericPrv))
      Coefficient(numRes, denomRes, Some(prvRes))
    }

    def *(that: Coefficient) : Coefficient = {
      val numRes = BigDecimalQETool.eval(Times(Number(num), Number(that.num)))
      val denomRes = BigDecimalQETool.eval(Times(Number(denom), Number(that.denom)))
      val inst = Seq(
        ("ln_", numN),
          ("ld_", denomN),
          ("rn_", that.numN),
          ("rd_", that.denomN),
          ("l_", lhs),
          ("r_", that.lhs),
          ("pn_", Number(numRes)),
          ("pd_", Number(denomRes)))
      val numericPrv = ProvableSig.proveArithmetic(BigDecimalQETool,
        List(
          Equal(Times(numN, that.numN), Number(numRes)),
          Equal(Times(denomN, that.denomN), Number(denomRes)),
          NotEqual(denomN, Number(0)),
          NotEqual(that.denomN, Number(0)),
        ).reduceRight(And)
      )
      val prvRes = useDirectly(coefficientTimesPrv, inst, Seq(prv, that.prv, numericPrv))
      Coefficient(numRes, denomRes, Some(prvRes))
    }

    def bigDecimalOption : Option[ProvableSig] = {
      val d = Divide(numN, denomN)
      (try {
        Some(Number(BigDecimalQETool.eval(d)))
      } catch {
        case _: IllegalArgumentException => None
      }).map{bd =>
        useDirectly(coefficientBigDecimalPrv,
          Seq(("x_", lhs), ("xn_", numN), ("xd_", denomN), ("bd_", bd)),
          Seq(prv, ProvableSig.proveArithmetic(BigDecimalQETool, And(Equal(d, bd), NotEqual(denomN, Number(0))))))
      }
    }

    /** normalized to a nicer output form, i.e., simplify rhs with
      *   0 / d = 0
      *   n / d = bd
      * */
    def normalized : (ProvableSig, Term) = if (num.compareTo(0) == 0) {
      (useDirectly(normalizeCoeff0, Seq(("c_", lhs), ("d_", denomN)), Seq(prv)), Number(0))
    } else bigDecimalOption match {
      case Some(prv) => (prv, rhsOf(prv))
      case None => (prv, rhs)
    }

    def split(newNum: BigDecimal, newdenom: BigDecimal) : (ProvableSig, Coefficient, Coefficient) = {
      val num1 = newNum
      val denom1 = newdenom
      val num2 = num * denom1 - num1 * denom
      val denom2 = denom * denom1
      val numericCondition = ProvableSig.proveArithmetic(BigDecimalQETool,
        splitCoefficientNumericCondition(numN, denomN, Number(num1), Number(denom1), Number(num2), Number(denom2)))
      (useDirectly(splitCoefficient, Seq(("c_", lhs), ("n_", numN), ("d_", denomN),
        ("n1_", Number(num1)), ("d1_", Number(denom1)),
        ("n2_", Number(num2)), ("d2_", Number(denom2)),
      ), Seq(prv, numericCondition)),
        Coefficient(num1, denom1), Coefficient(num2, denom2))
    }

    def approx(prec: Int) : (ProvableSig, Coefficient, Coefficient) = {
      val (l, _) = IntervalArithmeticV2.eval_ivl(prec-1)(HashMap(), HashMap())(rhs)
      split(l, 1) // @note: this is round to negative infinity - does it matter?
    }

  }

  lazy val identityTimes = anyArgify(Ax.identityTimes)
  lazy val timesIdentity = anyArgify(Ax.timesIdentity)
  lazy val divideIdentity = anyArgify(Ax.divideIdentity)

  lazy val plusTimes = anyArgify(Ax.plusTimes)
  lazy val negTimes = anyArgify(Ax.negTimes)

  lazy val powerLemma = anyArgify(Ax.powerLemma)
  private def mkConstN(s: String, i: Int) = s + i.toString + "_"
  private def mkConst(s: String, i: Int) = FuncOf(Function(mkConstN(s, i), None, Unit, Real), Nothing)

  /**
    * l = cl * xls
    * r = cr * xrs
    * c = cl*cr
    * xs = xls ** xrs
    * ->
    * l*r=c*xs
    * */
  lazy val monomialTimesLemma = anyArgify(Ax.monomialTimesLemma.provable)

  lazy val timesPowersBoth = anyArgify(Ax.timesPowersBoth.provable)

  lazy val timesPowersLeft = anyArgify(Ax.timesPowersLeft.provable)

  lazy val timesPowersRight = anyArgify(Ax.timesPowersRight.provable)
  lazy val timesPowers1Right = anyArgify(Ax.timesPowers1Right.provable)
  lazy val timesPowers1Left = anyArgify(Ax.timesPowers1Left.provable)

  val constF = anyR("f_")
  val constX = anyR("x_")

  /**
    * prv: lhs = rhs
    * lhs: input term (arbitrary, trace of construction)
    * rhs: representation of `coeff*powers.map(^)`
    *
    * */
  case class Monomial(coeff: Coefficient, powerProduct: SparsePowerProduct, prvO: Option[ProvableSig] = None) {
    val powers = powerProduct.sparse.toIndexedSeq
    lazy val powersTerm: Term = powers.map{case (v, i) => Power(v, Number(i))}.foldLeft(Number(1): Term)(Times)

    def monomialTerm(coeff: Term): Term = Times(coeff, powersTerm)

    def powersString: String = {
      val sep = " " // nicer than "*" ?
      (if (coeff.num.compareTo(1) == 0 && coeff.denom.compareTo(1) == 0 && powers.exists(_._2 > 0)) ""
      else if (coeff.num.compareTo(-1) == 0 && coeff.denom.compareTo(1) == 0) "-"
      else coeff.rhsString + sep) +
        powers.map{case (v, p) => Power(v, Number(p))}.mkString(sep)
    }

    lazy val defaultPrv = equalReflex(monomialTerm(coeff.rhs))

    def forgetPrv = Monomial(coeff, powerProduct, Some(defaultPrv))

    // @note detour for "dependent" default argument
    val prv = prvO.getOrElse(defaultPrv)

    // @todo: finish proof!
    //assert(prv.subgoals.isEmpty)
    assert(prv.conclusion.ante.isEmpty)
    assert(prv.conclusion.succ.length == 1)
    assert(prv.conclusion.succ(0) match {
      case Equal(_, rhs) => rhs == monomialTerm(coeff.rhs)
      case _ => false
    })
    val (eq, lhs, rhs) = prv.conclusion.succ(0) match {
      case eq@Equal(lhs, rhs@(Times(_, _))) => (eq, lhs, rhs)
    }

    // return data structure for this.powers * "other.powers"
    // and proof for this.powersTerm * other.powersTerm
    def timesPowers(otherPowers: IndexedSeq[(Term, Int)]) : (IndexedSeq[(Term, Int)], ProvableSig) = {
      def rec(l: Int, r: Int) : (IndexedSeq[(Term, Int)], ProvableSig) = {
        if (l >= 0 && r >= 0) {
          val (x, i) = powers(l)
          val (y, j) = otherPowers(r)
          variableOrdering.compare(x, y) match {
            case c if c == 0 =>
              val (recPowers, recPrv) = rec(l-1, r-1)
              val Times(xs, ys) = lhsOf(recPrv)
              val xys = rhsOf(recPrv)
              val k = i + j
              val numPrv =
                ProvableSig.proveArithmetic(BigDecimalQETool,
                  Seq(GreaterEqual(Number(i), Number(0)),
                    GreaterEqual(Number(j), Number(0)),
                    Equal(Plus(Number(i), Number(j)), Number(k))).reduceRight(And))
              val newPrv = useDirectly(timesPowersBoth,
                Seq(("i_", Number(i)),
                  ("j_", Number(j)),
                  ("k_", Number(k)),
                  ("xs_", xs),
                  ("ys_", ys),
                  ("xys_", xys),
                  ("x_", x)
                ), Seq(numPrv, recPrv))
              (recPowers :+ (x, k), newPrv)
            case c if c < 0 =>
              val (recPowers, recPrv) = rec(l, r-1)
              val Times(xs, ys) = lhsOf(recPrv)
              val xys = rhsOf(recPrv)
              val newPrv = useDirectly(timesPowersRight,
                Seq(("xs_", xs),
                  ("ys_", ys),
                  ("xys_", xys),
                  ("y_", Power(y, Number(j)))
                ), Seq(recPrv))
              (recPowers :+ (y, j), newPrv)
            case c if c > 0 =>
              val (recPowers, recPrv) = rec(l-1, r)
              val Times(xs, ys) = lhsOf(recPrv)
              val xys = rhsOf(recPrv)
              val newPrv = useDirectly(timesPowersLeft,
                Seq(
                  ("xs_", xs),
                  ("ys_", ys),
                  ("xys_", xys),
                  ("x_", Power(x, Number(i)))
                ), Seq(recPrv))
              (recPowers :+ (x, i), newPrv)
          }
        } else if (l >= 0) {
          val basePowers = powers.take(l+1)
          val xs = basePowers.map{case (v, p) => Power(v, Number(p))}.foldLeft[Term](Number(1))(Times)
          val newPrv = useDirectly(timesPowers1Right,
            Seq( ("xs_", xs) ), Seq())
          (basePowers, newPrv)
        } else {
          val basePowers = otherPowers.take(r+1)
          val ys = basePowers.map{case (v, p) => Power(v, Number(p))}.foldLeft[Term](Number(1))(Times)
          val newPrv = useDirectly(timesPowers1Left,
            Seq( ("ys_", ys) ), Seq())
          (basePowers, newPrv)
        }
      }
      rec(powers.length - 1, otherPowers.length - 1)
    }

    def *(that: Monomial): Monomial = {
      val newCoeff = coeff.forgetPrv * that.coeff.forgetPrv
      val (newPowers, newPowersPrv) = timesPowers(that.powers)
      // TODO: just use a match for simplicity?
      val inst = Seq(("l_", lhs),
        ("r_", that.lhs),
        ("cl_", coeff.rhs),
        ("cr_", that.coeff.rhs),
        ("xls_", powersTerm),
        ("xrs_", that.powersTerm),
        ("c_", newCoeff.rhs),
        ("xs_", rhsOf(newPowersPrv))
      )
      val monomialTimesLemmaInst = monomialTimesLemma(substOfInst(inst))
      val newPrv = impliesElim(monomialTimesLemmaInst, Seq(prv, that.prv, newCoeff.prv, newPowersPrv))
      Monomial(newCoeff, wfPowerProduct(newPowers), Some(newPrv))
    }

    def unary_- : Monomial = {
      val newCoeff = -(coeff.forgetPrv)
      val newPrv = useDirectly(negTimes, Seq(("l_", lhs), ("a_", coeff.rhs), ("b_", rhs.right), ("c_", newCoeff.rhs)),
        Seq(prv, newCoeff.prv))
      Monomial(newCoeff, powerProduct, Some(newPrv))
    }

    // TODO: weird signature for addition...
    def +(that: Monomial): Option[Monomial] = if (that.powers == powers) Some {
      val newCoeff = coeff.forgetPrv + that.coeff.forgetPrv

      val inst = Seq(("l_", lhs), ("r_", that.lhs), ("a_", coeff.rhs), ("b_", rhs.right), ("c_", that.coeff.rhs), ("d_", newCoeff.rhs))
      val newPrv = useDirectly(plusTimes, inst, Seq(prv, that.prv, newCoeff.prv))
      Monomial(newCoeff, powerProduct, Some(newPrv))
    } else None

    def normalizePowers(c: Coefficient, t: Term): (ProvableSig, Term) = t match {
      case Times(Number(one), t@Power(v, Number(n))) =>
        //assert(one.compareTo(1)==0)
        val (cdPrv, d) = c.normalized
        if (c.num.compareTo(1) == 0 && c.denom.compareTo(1) == 0) {
          // c = 1
          if (n.compareTo(1) == 0) {
            (useDirectly(normalizePowers1V, Seq(("c_", c.lhs), ("v_", v)), Seq(cdPrv)), v)
          } else {
            (useDirectly(normalizePowers1R, Seq(("c_", c.lhs), ("t_", t)), Seq(cdPrv)), t)
          }
        } else {
          // c = d
          if (n.compareTo(1) == 0) {
            (useDirectly(normalizePowersCV, Seq(("c_", c.lhs), ("d_", d), ("v_", v)), Seq(cdPrv)), Times(d, v))
          } else {
            (useDirectly(normalizePowersCP, Seq(("c_", c.lhs), ("d_", d), ("t_", t)), Seq(cdPrv)), Times(d, t))
          }
        }
      case Times(ps, t@Power(v, Number(n))) =>
        val (cpsPrv, cps) = normalizePowers(c, ps)
        if (n.compareTo(1) == 0) {
          (useDirectly(normalizePowersRV, Seq(("c_", c.lhs), ("ps_", ps), ("cps_", cps), ("v_", v)), Seq(cpsPrv)), Times(cps, v))
        } else {
          (useDirectly(normalizePowersRP, Seq(("c_", c.lhs), ("ps_", ps), ("cps_", cps), ("t_", t)), Seq(cpsPrv)), Times(cps, t))
        }
      case Number(n) =>
        //assert((n.compareTo(1) == 0))
        val (cdPrv, d) = c.normalized
        (useDirectly(normalizePowersC1, Seq(("c_", c.lhs), ("d_", d)), Seq(cdPrv)), d)
    }

    /**
      * normalized: normalize coefficient, rewrite product of rhs with
      *   1 * x = x
      *   x * 1 = 1
      *   x ^ 1 = x
      * */
    def normalized : ProvableSig = {
      val (cnPrv, cn) = coeff.forgetPrv.normalized
      if (coeff.num.compareTo(0) == 0)
        useDirectly(normalizeMonom0, Seq(
          ("x_", lhs),
          ("c_", coeff.rhs),
          ("ps_", powersTerm)), Seq(prv, cnPrv))
      else if (coeff.num.compareTo(0) > 0) {
        val (cpsPrv, cps) = normalizePowers(coeff.forgetPrv, powersTerm)
        useDirectly(normalizeMonomCS, Seq(
          ("x_", lhs),
          ("c_", coeff.rhs),
          ("ps_", powersTerm),
          ("cps_", cps)
        ), Seq(prv, cpsPrv))
      } else {
        val m = -coeff.forgetPrv
        val (cpsPrv, cps) = normalizePowers(m.forgetPrv, powersTerm)
        useDirectly(normalizeMonomNCS, Seq(
          ("x_", lhs),
          ("c_", coeff.rhs),
          ("m_", m.rhs),
          ("ps_", powersTerm),
          ("cps_", cps)
        ), Seq(prv, m.prv, cpsPrv))
      }
    }

    def approx(prec: Int) : (ProvableSig, Monomial, Monomial) = {
      val (cPrv, c1, c2) = coeff.forgetPrv.approx(prec)
      (useDirectly(splitMonomial, Seq(("c_", coeff.rhs), ("x_", powersTerm), ("c1_", c1.rhs), ("c2_", c2.rhs), ("m_", lhs)),
        Seq(cPrv, prv)), Monomial(c1, powerProduct), Monomial(c2, powerProduct))
    }

    def isConstant = powers.forall{case (t, i) => i == 0 } || coeff.num.compare(0) == 0

    def degree(include: Term=>Boolean = _ => true) : Int =
      if (coeff.num.compare(0) != 0)
        powers.map{ case (t, p) => if (include(t)) p else 0 }.sum
      else 0

  }

  lazy val zez = anyArgify(Ax.zez.provable)

  lazy val emptySprout = anyArgify(Ax.emptySprout.provable)

  // Lemmas for insert (i.e., add monomial)

  // @todo: should these be constructed more systematically?! e.g., define common subformulas only once. would make the code more robust...
  lazy val branch2Left  = anyArgify(Ax.branch2Left .provable)
  lazy val branch2Value = anyArgify(Ax.branch2Value.provable)
  lazy val branch2Right = anyArgify(Ax.branch2Right.provable)

  /** @note for the Left case, could actually just use [[branch2Left]] */
  lazy val branch2GrowLeft =  anyArgify(Ax.branch2GrowLeft.provable)
  lazy val branch2GrowRight = anyArgify(Ax.branch2GrowRight.provable)

  lazy val branch3Left = anyArgify(Ax.branch3Left.provable)
  lazy val branch3Value1 = anyArgify(Ax.branch3Value1.provable)
  lazy val branch3Mid =    anyArgify(Ax.branch3Mid.provable)
  lazy val branch3Value2 = anyArgify(Ax.branch3Value2.provable)
  lazy val branch3Right =  anyArgify(Ax.branch3Right.provable)

  lazy val branch3GrowLeft = anyArgify(Ax.branch3GrowLeft.provable)

  lazy val branch3GrowMid = anyArgify(Ax.branch3GrowMid.provable)
  lazy val branch3GrowRight = anyArgify(Ax.branch3GrowRight.provable)

  // Lemmas for Add
  lazy val plusEmpty = anyArgify(Ax.plusEmpty.provable)
  lazy val plusBranch2 = anyArgify(Ax.plusBranch2.provable)
  lazy val plusBranch3 = anyArgify(Ax.plusBranch3.provable)

  // Lemmas for Minus
  lazy val minusEmpty = anyArgify(Ax.minusEmpty.provable)
  lazy val minusBranch2 = anyArgify(Ax.minusBranch2.provable)
  lazy val minusBranch3 = anyArgify(Ax.minusBranch3.provable)

  // Lemmas for Minus Monomial
  lazy val plusMinus = anyArgify(Ax.plusMinus.provable)

  // Lemmas for Times Monomial
  lazy val monTimesZero = anyArgify(Ax.monTimesZero.provable)
  lazy val monTimesBranch2 = anyArgify(Ax.monTimesBranch2.provable)
  lazy val monTimesBranch3 = anyArgify(Ax.monTimesBranch3.provable)

  // Lemmas for Times
  lazy val timesEmpty = anyArgify(Ax.timesEmpty.provable)
  lazy val timesBranch2 = anyArgify(Ax.timesBranch2.provable)
  lazy val timesBranch3 = anyArgify(Ax.timesBranch3.provable)

  // Lemmas for Power
  lazy val powerZero = anyArgify(Ax.powerZero.provable)
  lazy val powerOne = anyArgify(Ax.powerOne.provable)
  lazy val powerEven = anyArgify(Ax.powerEven.provable)
  lazy val powerOdd = anyArgify(Ax.powerOdd.provable)
  lazy val powerPoly = anyArgify(Ax.powerPoly.provable)

  // Lemmas for division
  lazy val divideNumber = anyArgify(Ax.divideNumber.provable)
  lazy val divideRat = anyArgify(Ax.divideRat.provable)
  lazy val divideNeg = anyArgify(Ax.divideNeg.provable)

  // Lemmas for negation
  lazy val negateEmpty = anyArgify(Ax.negateEmpty.provable)
  lazy val negateBranch2 = anyArgify(Ax.negateBranch2.provable)
  lazy val negateBranch3 = anyArgify(Ax.negateBranch3.provable)


  // Lemmas for normalization
  lazy val normalizeCoeff0 = anyArgify(Ax.normalizeCoeff0.provable)
  lazy val normalizeCoeff1 = anyArgify(Ax.normalizeCoeff1.provable)

  lazy val normalizeMonom0 = anyArgify(Ax.normalizeMonom0.provable)
  lazy val normalizeMonomCS = anyArgify(Ax.normalizeMonomCS.provable)
  lazy val normalizeMonomNCS = anyArgify(Ax.normalizeMonomNCS.provable)

  lazy val normalizePowers1V = anyArgify(Ax.normalizePowers1V.provable)
  lazy val normalizePowers1R = anyArgify(Ax.normalizePowers1R.provable)
  lazy val normalizePowersC1 = anyArgify(Ax.normalizePowersC1.provable)
  lazy val normalizePowersCV = anyArgify(Ax.normalizePowersCV.provable)
  lazy val normalizePowersCP = anyArgify(Ax.normalizePowersCP.provable)
  lazy val normalizePowersRV = anyArgify(Ax.normalizePowersRV.provable)
  lazy val normalizePowersRP = anyArgify(Ax.normalizePowersRP.provable)

  lazy val normalizeBranch2 = anyArgify(Ax.normalizeBranch2.provable)
  lazy val normalizeBranch3 = anyArgify(Ax.normalizeBranch3.provable)

  lazy val reassocRight0 = anyArgify(Ax.reassocRight0.provable)
  lazy val reassocRightPlus = anyArgify(Ax.reassocRightPlus.provable)
  lazy val reassocLeft0RightConst = anyArgify(Ax.reassocLeft0RightConst.provable)
  lazy val reassocRightConst = anyArgify(Ax.reassocRightConst.provable)

  // lemmas to prove equality
  lazy val equalityBySubtraction = anyArgify(Ax.equalityBySubtraction.provable)

  // Lemmas for partition
  lazy val partition2 = anyArgify(Ax.partition2.provable)

  // Lemmas for splitting coefficients
  @inline
  private def nz(t: Term) : Formula = NotEqual(t, Number(0))
  // @todo: compute ``instantiations'' like this everywhere and prove by matching?
  def splitCoefficientNumericCondition(n: Term, d: Term, n1: Term, d1: Term, n2: Term, d2: Term) =
    And(Equal(Times(Times(n, d1), d2), Times(d, Plus(Times(d1, n2), Times(d2, n1)))), And(nz(d), And(nz(d1), nz(d2))))

  lazy val splitCoefficient = anyArgify(Ax.splitCoefficient.provable)
  lazy val splitMonomial = anyArgify(Ax.splitMonomial.provable)
  lazy val splitEmpty  = anyArgify(Ax.splitEmpty .provable)
  lazy val splitBranch2  = anyArgify(Ax.splitBranch2 .provable)
  lazy val splitBranch3  = anyArgify(Ax.splitBranch3 .provable)


  /** drop parentheses of a sum of terms on the rhs of prv to the left, e.g.,
    * t = a + (b + c) ~~> t = a + b + c
    * */
  def reassoc(prv: ProvableSig) : ProvableSig = rhsOf(prv) match {
    case Plus(l, r) =>
      val rPrv = reassoc(equalReflex(r))
      rhsOf(rPrv) match {
        case Number(n) if n.compareTo(0) == 0 =>
          val llPrv = reassoc(equalReflex(l))
          useDirectly(reassocRight0, Seq(
            ("t_", lhsOf(prv)),
            ("l_", l),
            ("r_", r),
            ("ll_", rhsOf(llPrv))
          ), Seq(prv, rPrv, llPrv))
        case Plus(rs, rr) =>
          val lrsPrv = reassoc(equalReflex(Plus(l, rs)))
          useDirectly (reassocRightPlus, Seq(
            ("t_", lhsOf(prv)),
            ("l_", l),
            ("r_", r),
            ("rs_", rs),
            ("rr_", rr),
            ("lrs_", rhsOf(lrsPrv))
          ), Seq(prv, rPrv, lrsPrv))
        case c =>
          val llPrv = reassoc(equalReflex(l))
          rhsOf(llPrv) match {
            case Number(n) if n.compareTo(0) == 0 =>
              useDirectly (reassocLeft0RightConst, Seq(
                ("t_", lhsOf(prv)),
                ("l_", l),
                ("r_", r),
                ("c_", c)
              ), Seq(prv, rPrv, llPrv))
            case ll =>
              useDirectly (reassocRightConst, Seq(
                ("t_", lhsOf(prv)),
                ("l_", l),
                ("r_", r),
                ("c_", c),
                ("ll_", ll)
              ), Seq(prv, rPrv, llPrv))
          }
      }
    case _ =>
      prv
  }

  /**
    * 2-3 Tree for monomials, keeping track of proofs.
    * */
  sealed trait Growth
  case class Stay(p: TreePolynomial) extends Growth
  case class Sprout(sprout: Branch2) extends Growth

  final case class UnknownPolynomialImplementationException(other: Polynomial) extends
    RuntimeException("only TreePolynomials are supported, but got " + other)

  lazy val equalReflexive = Ax.equalReflexive.provable

  sealed trait TreePolynomial extends Polynomial {
    val prv: ProvableSig
    override def representation: ProvableSig = prv
    def forgetPrv: TreePolynomial
    override def resetTerm: Polynomial = forgetPrv
    override def prettyTerm : Polynomial = {
      val repr = representation
      val prettyRepr = prettyRepresentation
      val prettyPrv = proveBy(Equal(PolynomialArithV2Helpers.rhsOf(prettyRepr), PolynomialArithV2Helpers.rhsOf(repr)),
        useAt(repr, PosInExpr(1::Nil))(1, 1::Nil) &
          useAt(prettyRepr, PosInExpr(1::Nil))(1, 0::Nil) &
          byUS(equalReflexive)
      )
      resetRepresentation(prettyPrv)
    }

    def treeSketch: String
    lazy val (eq, lhs, rhs) = prv.conclusion.succ(0) match { case eq @ Equal(lhs, rhs) => (eq, lhs, rhs) }
    lazy val term = lhs

    def lookup(x: IndexedSeq[(Term, Int)]) : Option[Monomial] = this match {
      case Empty(_) => None
      case Branch2(left, v, right, _) => monomialOrdering.compare(x, v.powers) match {
        case 0 => Some(v)
        case c if c < 0 => left.lookup(x)
        case c if c > 0 => right.lookup(x)
      }
      case Branch3(left, v1, mid, v2, right, _) => monomialOrdering.compare(x, v1.powers)  match {
        case 0 => Some(v1)
        case c if c < 0 => left.lookup(x)
        case c if c > 0 => monomialOrdering.compare(x, v2.powers)  match {
          case 0 => Some(v2)
          case c if c < 0 => mid.lookup(x)
          case c if c > 0 => right.lookup(x)
        }
      }
    }


    // addition

    private def insert(x: Monomial) : Growth = this match {
      case Empty(_) =>
        val newPrv = useDirectly(emptySprout, Seq(("s_", lhs),("t_", x.lhs),("u_", x.rhs)), Seq(prv, x.prv))
        Sprout(Branch2(Empty(None), x, Empty(None), Some(newPrv)))
      case tree @ Branch2(left, v, right, prv) =>
        val newLhs = Plus(tree.lhs, x.lhs)
        val treeInst = IndexedSeq(
          ("t_", tree.lhs),
          ("v_", v.rhs),
          ("x_", x.lhs),
          ("l_", left.rhs),
          ("r_", right.rhs)
        )
        monomialOrdering.compare(x.powers, v.powers)  match {
        case 0 =>
          val vx = (v.forgetPrv+x).getOrElse(throw new IllegalArgumentException(v.forgetPrv.powersTerm + " and " + x.powersTerm + " do not fit"))
          val newRhs = Plus(Plus(left.rhs, vx.rhs), right.rhs)
          val newPrv = useDirectly(branch2Value, treeInst ++ Seq(("vx_", vx.rhs)), Seq(tree.prv, vx.prv))
          Stay(Branch2(left, vx, right, Some(newPrv)))
        case c if c < 0 => {
          left.forgetPrv.insert(x) match {
            case Sprout(lx) =>
              val l1 = lx.left.rhs
              val lv = lx.value.rhs
              val l2 = lx.right.rhs
              val newRhs = Seq(l1, lv, l2, v.rhs, right.rhs).reduceLeft(Plus)
              val newPrv = useDirectly(branch2GrowLeft, treeInst ++ Seq(("l1_", l1), ("lv_", lv) , ("l2_", l2)), Seq(tree.prv, lx.prv))
              Stay(Branch3(lx.left, lx.value, lx.right, v, right, Some(newPrv)))
            case Stay(lx) =>
              val newRhs = Plus(Plus(lx.rhs, v.rhs), right.rhs)
              val newPrv = useDirectly(branch2Left, treeInst ++ Seq(("lx_", lx.rhs)), Seq(tree.prv, lx.prv))
              Stay(Branch2(lx, v, right, Some(newPrv)))
          }
        }
        case c if c > 0 =>  {
          right.forgetPrv.insert(x) match {
            case Sprout(rx) =>
              val r1 = rx.left.rhs
              val rv = rx.value.rhs
              val r2 = rx.right.rhs
              val newRhs = Seq(left.rhs, v.rhs, r1, rv, r2).reduceLeft(Plus)
              val newPrv = useDirectly(branch2GrowRight, treeInst ++ Seq(("r1_", r1),("rv_", rv),("r2_", r2)), Seq(tree.prv, rx.prv))
              Stay(Branch3(left, v, rx.left, rx.value, rx.right, Some(newPrv)))
            case Stay(rx) =>
              val newRhs = Plus(Plus(left.rhs, v.rhs), rx.rhs)
              val newPrv = useDirectly(branch2Right, treeInst ++ Seq(("rx_", rx.rhs)), Seq(tree.prv, rx.prv))
              Stay(Branch2(left, v, rx, Some(newPrv)))
          }
        }
      }
      case tree @ Branch3(left, v, mid, w, right, prv) =>
        val newLhs = Plus(tree.lhs, x.lhs)
        val treeInst = IndexedSeq(
          ("t_", tree.lhs),
          ("x_", x.lhs),
          ("l_", left.rhs),
          ("v_", v.rhs),
          ("m_", mid.rhs),
          ("w_", w.rhs),
          ("r_", right.rhs)
        )
        monomialOrdering.compare(x.powers, v.powers)  match {
          case 0 =>
            val vx = (v.forgetPrv + x).get
            val newRhs = Seq(left.rhs, vx.rhs, mid.rhs, w.rhs, right.rhs).reduceLeft(Plus)
            val newPrv = useDirectly(branch3Value1, treeInst ++ Seq(("vx_", vx.rhs)), Seq(tree.prv, vx.prv))
            Stay(Branch3(left, vx, mid, w, right, Some(newPrv)))
          case c if c < 0 => left.forgetPrv.insert(x) match {
            case Stay(lx) =>
              val newRhs = Seq(lx.rhs, v.rhs, mid.rhs, w.rhs, right.rhs).reduceLeft(Plus)
              val newPrv = useDirectly(branch3Left, treeInst ++ Seq(("lx_", lx.rhs)), Seq(tree.prv, lx.prv))
              Stay(Branch3(lx, v, mid, w, right, Some(newPrv)))
            case Sprout(lx) =>
              val l1 = lx.left.rhs
              val lv = lx.value.rhs
              val l2 = lx.right.rhs
              val newRhs = Seq(Seq(l1, lv, l2).reduceLeft(Plus), v.rhs, Seq(mid.rhs, w.rhs, right.rhs).reduceLeft(Plus)).reduceLeft(Plus)
              val newPrv = useDirectly(branch3GrowLeft, treeInst ++ Seq(("l1_", l1), ("lv_", lv), ("l2_", l2)), Seq(tree.prv, lx.prv))
              Sprout(Branch2(lx, v, Branch2(mid, w, right, None), Some(newPrv)))
          }
          case c if c > 0 =>
            monomialOrdering.compare(x.powers, w.powers)  match {
              case 0 =>
                val wx = (w.forgetPrv + x).get
                val newRhs = Seq(left.rhs, v.rhs, mid.rhs, wx.rhs, right.rhs).reduceLeft(Plus)
                val newPrv = useDirectly(branch3Value2, treeInst ++ Seq(("wx_", wx.rhs)), Seq(tree.prv, wx.prv))
                Stay(Branch3(left, v, mid, wx, right, Some(newPrv)))
              case c if c < 0 =>
                mid.forgetPrv.insert(x) match {
                  case Stay(mx) =>
                    val newRhs = Seq(left.rhs, v.rhs, mx.rhs, w.rhs, right.rhs).reduceLeft(Plus)
                    val newPrv = useDirectly(branch3Mid, treeInst ++ Seq(("mx_", mx.rhs)), Seq(tree.prv, mx.prv))
                    Stay(Branch3(left, v, mx, w, right, Some(newPrv)))
                  case Sprout(mx) =>
                    val m1 = mx.left.rhs
                    val mv = mx.value.rhs
                    val m2 = mx.right.rhs
                    val newRhs = Seq(Seq(left.rhs, v.rhs, m1).reduceLeft(Plus), mv, Seq(m2, w.rhs, right.rhs).reduceLeft(Plus)).reduceLeft(Plus)
                    val newPrv = useDirectly(branch3GrowMid, treeInst ++ Seq(("m1_", m1), ("mv_", mv), ("m2_", m2)), Seq(tree.prv, mx.prv))
                    Sprout(Branch2(Branch2(left, v, mx.left, None), mx.value, Branch2(mx.right, w, right, None), Some(newPrv)))
                }
              case c if c > 0 =>
                right.forgetPrv.insert(x) match {
                  case Stay(rx) =>
                    val newRhs = Seq(left.rhs, v.rhs, mid.rhs, w.rhs, rx.rhs).reduceLeft(Plus)
                    val newPrv = useDirectly(branch3Right, treeInst ++ Seq(("rx_", rx.rhs)), Seq(tree.prv, rx.prv))
                    Stay(Branch3(left, v, mid, w, rx, Some(newPrv)))
                  case Sprout(rx) =>
                    val r1 = rx.left.rhs
                    val rv = rx.value.rhs
                    val r2 = rx.right.rhs
                    val newRhs = Seq(Seq(left.rhs, v.rhs, mid.rhs).reduceLeft(Plus), w.rhs, Seq(r1, rv, r2).reduceLeft(Plus)).reduceLeft(Plus)
                    val newPrv = useDirectly(branch3GrowRight, treeInst ++ Seq(("r1_", r1), ("rv_", rv), ("r2_", r2)), Seq(tree.prv, rx.prv))
                    Sprout(Branch2(Branch2(left, v, mid, None), w, rx, Some(newPrv)))
                }
            }
        }
    }
    def +(m: Monomial) : TreePolynomial = insert(m) match {
      case Stay(p) => p
      case Sprout(s) => s
    }

    def -(m: Monomial) : TreePolynomial = {
      val res = this + (-(m.forgetPrv))
      res.updatePrv(useDirectly(plusMinus, Seq(("t_", lhs), ("x_", m.lhs), ("s_", res.rhs)), Seq(res.prv)))
    }

    private[TwoThreeTreePolynomialRing] def updatePrv(prv2: ProvableSig) : TreePolynomial = {
      this match {
        case Empty(_) => Empty(Some(prv2))
        case Branch2(l, v, m, _) => Branch2(l, v, m, Some(prv2))
        case Branch3(l, v1, m, v2, r, _) => Branch3(l, v1, m, v2, r, Some(prv2))
      }
    }

    def +(other: Polynomial) : TreePolynomial = other match {
      case other @ Empty(_) =>
        val newPrv = useDirectly(plusEmpty, Seq(("t_", lhs), ("s_", rhs), ("u_", other.lhs)), Seq(prv, other.prv))
        updatePrv(newPrv)
      case other @ Branch2(left, value, right, _) =>
        val sum = this + left.forgetPrv + value.forgetPrv + right.forgetPrv
        val newPrv = useDirectly(plusBranch2, IndexedSeq(
            ("t_", lhs),
            ("s_", other.lhs),
            ("l_", left.rhs),
            ("v_", value.rhs),
            ("r_", right.rhs),
            ("sum_", sum.rhs)
          ), Seq(other.prv, sum.prv))
        sum.updatePrv(newPrv)
      case other @ Branch3(left, value1, mid, value2, right, _) =>
        val sum = this + left.forgetPrv + value1.forgetPrv + mid.forgetPrv + value2.forgetPrv + right.forgetPrv
        val newPrv = useDirectly(plusBranch3, IndexedSeq(
            ("t_", lhs),
            ("s_", other.lhs),
            ("l_", left.rhs),
            ("v1_", value1.rhs),
            ("m_", mid.rhs),
            ("v2_", value2.rhs),
            ("r_", right.rhs),
            ("sum_", sum.rhs)
          ), Seq(other.prv, sum.prv))
        sum.updatePrv(newPrv)
      case _ => throw UnknownPolynomialImplementationException(other: Polynomial)
    }

    def -(other: Polynomial) : TreePolynomial = other match {
      case other @ Empty(_) =>
        val newPrv = useDirectly(minusEmpty, Seq(("t_", lhs), ("s_", rhs), ("u_", other.lhs)), Seq(prv, other.prv))
        updatePrv(newPrv)
      case other @ Branch2(left, value, right, _) =>
        val sum = this - left.forgetPrv - value.forgetPrv - right.forgetPrv
        val newPrv = useDirectly(minusBranch2, IndexedSeq(
          ("t_", lhs),
          ("s_", other.lhs),
          ("l_", left.rhs),
          ("v_", value.rhs),
          ("r_", right.rhs),
          ("sum_", sum.rhs)
        ), Seq(other.prv, sum.prv))
        sum.updatePrv(newPrv)
      case other @ Branch3(left, value1, mid, value2, right, _) =>
        val sum = this - left.forgetPrv - value1.forgetPrv - mid.forgetPrv - value2.forgetPrv - right.forgetPrv
        val newPrv = useDirectly(minusBranch3, IndexedSeq(
          ("t_", lhs),
          ("s_", other.lhs),
          ("l_", left.rhs),
          ("v1_", value1.rhs),
          ("m_", mid.rhs),
          ("v2_", value2.rhs),
          ("r_", right.rhs),
          ("sum_", sum.rhs)
        ), Seq(other.prv, sum.prv))
        sum.updatePrv(newPrv)
      case _ => throw UnknownPolynomialImplementationException(other: Polynomial)
    }

    def *(x: Monomial) : TreePolynomial = this match {
      case Empty(_) =>
        val newPrv = useDirectly(monTimesZero, Seq(("t_", lhs), ("x_", x.lhs)), Seq(prv))
        Empty(Some(newPrv))
      case Branch2(l, v, r, _) =>
        val lx = l.forgetPrv * x
        val vx = v.forgetPrv * x
        val rx = r.forgetPrv * x
        val newPrv = useDirectly(monTimesBranch2, IndexedSeq(
            ("t_", lhs),
            ("x_", x.lhs),
            ("l_", l.rhs),
            ("v_", v.rhs),
            ("r_", r.rhs),
            ("lx_", lx.rhs),
            ("vx_", vx.rhs),
            ("rx_", rx.rhs)), Seq(prv, lx.prv, vx.prv, rx.prv))
        Branch2(lx, vx, rx, Some(newPrv))
      case Branch3(l, v1, m, v2, r, _) =>
        val lx = l.forgetPrv * x
        val v1x = v1.forgetPrv * x
        val mx = m.forgetPrv * x
        val v2x = v2.forgetPrv * x
        val rx = r.forgetPrv * x
        val newPrv = useDirectly(monTimesBranch3, IndexedSeq(
            ("t_", lhs),
            ("x_", x.lhs),
            ("l_", l.rhs),
            ("v1_", v1.rhs),
            ("m_", m.rhs),
            ("v2_", v2.rhs),
            ("r_", r.rhs),
            ("lx_", lx.rhs),
            ("v1x_", v1x.rhs),
            ("mx_", mx.rhs),
            ("v2x_", v2x.rhs),
            ("rx_", rx.rhs)
          ), Seq(prv, lx.prv, v1x.prv, mx.prv, v2x.prv, rx.prv))
        Branch3(lx, v1x, mx, v2x, rx, Some(newPrv))
    }

    def *(other: Polynomial): TreePolynomial = other match {
      case other: TreePolynomial =>
        this match {
          case Empty(_) =>
            val newPrv = useDirectly(timesEmpty, Seq(("t_", lhs), ("u_", other.lhs)), Seq(prv))
            updatePrv(newPrv)
          case Branch2(left, value, right, _) =>
            val sum = (left.forgetPrv * other) + (other * value.forgetPrv) + (right.forgetPrv * other)
            val newPrv = useDirectly(timesBranch2, IndexedSeq(
              ("t_", lhs),
              ("u_", other.lhs),
              ("l_", left.rhs),
              ("v_", value.rhs),
              ("r_", right.rhs),
              ("sum_", sum.rhs)
            ), Seq(prv, sum.prv))
            sum.updatePrv(newPrv)
          case Branch3(left, value1, mid, value2, right, _) =>
            val sum = (left.forgetPrv * other) + (other * value1.forgetPrv) + (mid.forgetPrv * other) + (other * value2.forgetPrv) + (right.forgetPrv * other)
            val newPrv = useDirectly(timesBranch3, IndexedSeq(
              ("t_", lhs),
              ("u_", other.lhs),
              ("l_", left.rhs),
              ("v1_", value1.rhs),
              ("m_", mid.rhs),
              ("v2_", value2.rhs),
              ("r_", right.rhs),
              ("sum_", sum.rhs)
            ), Seq(prv, sum.prv))
            sum.updatePrv(newPrv)
        }
      case _ => throw UnknownPolynomialImplementationException(other: Polynomial)
    }

    def ^(n: Int) : TreePolynomial = n match {
      case 0 =>
        One.updatePrv(useDirectly(powerZero, IndexedSeq(("t_", lhs), ("one_", One.rhs)), Seq(One.prv)))
      case 1 =>
        this.updatePrv(useDirectly(powerOne, IndexedSeq(("t_", lhs), ("s_", rhs)), Seq(prv)))
      case n =>
        if (n >= 0) {
          if (n % 2 == 0) {
            val m = n / 2
            val mPrv = ProvableSig.proveArithmetic(BigDecimalQETool, Equal(Number(n), Times(Number(2), Number(m))))
            val p = this^(m)
            val r = p.forgetPrv*p.forgetPrv
            val newPrv = useDirectly(powerEven,
              Seq(("n_", Number(n)), ("m_", Number(m)), ("t_", lhs), ("p_", p.rhs), ("r_", r.rhs)),
              Seq(mPrv, p.prv, r.prv))
            r.updatePrv(newPrv)
          } else {
            val m = n / 2
            val mPrv = ProvableSig.proveArithmetic(BigDecimalQETool, Equal(Number(n), Plus(Times(Number(2), Number(m)), Number(1))))
            val p = this^(m)
            val r = p.forgetPrv*p.forgetPrv*this
            val newPrv = useDirectly(powerOdd,
              Seq(("n_", Number(n)), ("m_", Number(m)), ("t_", lhs), ("p_", p.rhs), ("r_", r.rhs)),
              Seq(mPrv, p.prv, r.prv))
            r.updatePrv(newPrv)
          }
        } else throw NonSupportedExponentException("negative power unsupported by PolynomialArithV2")
    }

    def isConstant : Boolean = this match {
      case Empty(_) => true
      case Branch2(l, v, r, _) =>
        v.isConstant && l.isConstant && r.isConstant
      case Branch3(l, v1, m, v2, r, _) =>
        v1.isConstant && v2.isConstant && l.isConstant && m.isConstant && r.isConstant
    }

    def ^(other: Polynomial): TreePolynomial = other match {
      case other: TreePolynomial =>
        if (other.isConstant) {
          val otherNormalized = other.normalized
          rhsOf(otherNormalized) match {
            case Number(i) if i.isValidInt =>
              val pi = this ^ i.toIntExact
              val newPrv = useDirectly(powerPoly,
                Seq(
                  ("p_", lhs),
                  ("q_", other.lhs),
                  ("i_", Number(i)),
                  ("r_", rhsOf(pi.prv))
                ),
                Seq(otherNormalized, pi.prv)
              )
              pi.updatePrv(newPrv)
            case Number(bd) =>
              throw NonSupportedExponentException("Exponent must be integer but normalizes to " + bd)
            case d@Divide(l, r) =>
              throw NonSupportedExponentException("Exponent must be integer but normalizes to division " + d)
            case n@Neg(_) =>
              throw NonSupportedExponentException("Exponent must be non negative but normalizes to " + n)
            case _ => throw new RuntimeException("Constant polynomials must normalize to Number, Divide, or Neg.")
          }
        } else {
          throw NonSupportedExponentException("Exponent must be a constant polynomial.")
        }
      case _ => throw UnknownPolynomialImplementationException(other: Polynomial)
    }

    def /(other: Polynomial): TreePolynomial = other match {
      case other: TreePolynomial =>
        if (other.isConstant) {
          val otherNormalized = other.normalized
          rhsOf(otherNormalized) match {
            case Number(i) if i.compareTo(0) != 0 =>
              val pi = this * Const(1, i)
              val newPrv = useDirectly(divideNumber,
                Seq(
                  ("p_", lhs),
                  ("q_", other.lhs),
                  ("i_", Number(i)),
                  ("r_", rhsOf(pi.prv))
                ),
                Seq(otherNormalized, pi.prv)
              )
              pi.updatePrv(newPrv)
            case Divide(Number(n), Number(d)) =>
              val pi = this * Const(d, n)
              val newPrv = useDirectly(divideRat,
                Seq(
                  ("p_", lhs),
                  ("q_", other.lhs),
                  ("n_", Number(n)),
                  ("d_", Number(d)),
                  ("r_", rhsOf(pi.prv))
                ),
                Seq(otherNormalized, pi.prv)
              )
              pi.updatePrv(newPrv)
            case Neg(_) =>
              val npq = - (this / (-other))
              val newPrv = useDirectly(divideNeg,
                Seq(
                  ("p_", lhs),
                  ("q_", other.lhs),
                  ("r_", rhsOf(npq.prv))
                ),
                Seq(npq.prv)
              )
              npq.updatePrv(newPrv)
            case _ => throw new RuntimeException("Constant polynomials must normalize to Number, Divide, or Neg.")
          }
        } else {
          throw NonSupportedDivisorException(s"Divisor ${other.term} must be a constant polynomial.")
        }
      case _ => throw UnknownPolynomialImplementationException(other: Polynomial)
    }

    // negation
    def unary_- : TreePolynomial = this match {
      case Empty(_) => Empty(Some(useDirectly(negateEmpty, Seq(("t_", lhs)), Seq(prv))))
      case Branch2(l, v, r, _) =>
        val nl = -(l.forgetPrv)
        val nv = -(v.forgetPrv)
        val nr = -(r.forgetPrv)
        val newPrv = useDirectly(negateBranch2, Seq(
          ("t_", lhs),
          ("l_", l.rhs),
          ("v_", v.rhs),
          ("r_", r.rhs),
          ("nl_", nl.rhs),
          ("nv_", nv.rhs),
          ("nr_", nr.rhs),
        ), Seq(prv, nl.prv, nv.prv, nr.prv))
        Branch2(nl, nv, nr, Some(newPrv))
      case Branch3(l, v1, m, v2, r, _) =>
        val nl = -(l.forgetPrv)
        val nv1 = -(v1.forgetPrv)
        val nm = -(m.forgetPrv)
        val nv2 = -(v2.forgetPrv)
        val nr = -(r.forgetPrv)
        val newPrv = useDirectly(negateBranch3, Seq(
          ("t_", lhs),
          ("l_", l.rhs),
          ("v1_", v1.rhs),
          ("m_", m.rhs),
          ("v2_", v2.rhs),
          ("r_", r.rhs),
          ("nl_", nl.rhs),
          ("nv1_", nv1.rhs),
          ("nm_", nm.rhs),
          ("nv2_", nv2.rhs),
          ("nr_", nr.rhs),
        ), Seq(prv, nl.prv, nv1.prv, nm.prv, nv2.prv, nr.prv))
        Branch3(nl, nv1, nm, nv2, nr, Some(newPrv))
    }


    /** only normalize monomials, keep 0s and binary tree association */
    def normalizedMonomials: ProvableSig = this match {
      case Empty(_) => prv
      case Branch2(l, v, r, _) =>
        val lnPrv = l.forgetPrv.normalizedMonomials
        val vnPrv = v.forgetPrv.normalized
        val rnPrv = r.forgetPrv.normalizedMonomials
        useDirectly(normalizeBranch2,
          Seq(
            ("t_", lhs),
            ("l_", l.rhs), ("v_", v.rhs), ("r_", r.rhs),
            ("ln_", rhsOf(lnPrv)), ("vn_", rhsOf(vnPrv)), ("rn_", rhsOf(rnPrv))
          ),
          Seq(prv, lnPrv, vnPrv, rnPrv))
      case Branch3(l, v1, m, v2, r, _) =>
        val lnPrv = l.forgetPrv.normalizedMonomials
        val v1nPrv = v1.forgetPrv.normalized
        val mnPrv = m.forgetPrv.normalizedMonomials
        val v2nPrv = v2.forgetPrv.normalized
        val rnPrv = r.forgetPrv.normalizedMonomials
        useDirectly(normalizeBranch3,
          Seq(
            ("t_", lhs),
            ("l_", l.rhs), ("v1_", v1.rhs), ("m_", m.rhs), ("v2_", v2.rhs), ("r_", r.rhs),
            ("ln_", rhsOf(lnPrv)), ("v1n_", rhsOf(v1nPrv)), ("mn_", rhsOf(mnPrv)), ("v2n_", rhsOf(v2nPrv)), ("rn_", rhsOf(rnPrv))
          ),
          Seq(prv, lnPrv, v1nPrv, mnPrv, v2nPrv, rnPrv))
    }

    /** normalized to nicer rhs: drop 0 for empty leaves, normalized monomials, reassociated
      * e.g., t = (0 + a + 0) + b + (0 + c + 0 + d + 0) ~~> t = a + b + c + d
      * */
    def normalized: ProvableSig = reassoc(normalizedMonomials)

    def prettyRepresentation: ProvableSig = normalized

    def zeroTest: Option[ProvableSig] = {
      val normalizedPrv = normalized
      rhsOf(normalizedPrv) match {
        case Number(n) if n.compareTo(0) == 0 =>
          Some(normalizedPrv)
        case _ => None
      }
    }

    override def equate(other: Polynomial): Option[ProvableSig] = other match {
      case other: TreePolynomial =>
        val diff = this - other
        diff.zeroTest match {
          case None => None
          case Some(zeroPrv) =>
            Some(useDirectly(equalityBySubtraction, Seq(("t_", this.lhs), ("s_", other.lhs)), Seq(zeroPrv)))
        }
      case _ => throw UnknownPolynomialImplementationException(other: Polynomial)
    }

    def partitionMonomials(P: Monomial => Boolean)(acc: (Seq[Monomial], Seq[Monomial])) : (Seq[Monomial], Seq[Monomial]) = {
      def accumulate(m: Monomial)(acc: (Seq[Monomial], Seq[Monomial])) :  (Seq[Monomial], Seq[Monomial]) = acc match {
        case (pos, neg) =>
          if (P(m)) (m +: pos, neg)
          else (pos, m +: neg)
      }
      this match {
        case Empty(_) => acc
        case Branch2(left, value, right, _) =>
          right.partitionMonomials(P)(accumulate(value)(left.partitionMonomials(P)(acc)))
        case Branch3(left, value1, mid, value2, right, _) =>
          right.partitionMonomials(P)(accumulate(value2)(mid.partitionMonomials(P)(accumulate(value1)(left.partitionMonomials(P)(acc)))))
      }
    }

    def ofMonomials(monomials: Seq[Monomial]): TreePolynomial = monomials.foldLeft[TreePolynomial](Empty(None))(_ + _)

    def partition(P: (BigDecimal, BigDecimal, PowerProduct) => Boolean): (Polynomial, Polynomial, ProvableSig) = {
      def PMonomial(m: Monomial) : Boolean = P(m.coeff.num, m.coeff.denom, m.powerProduct)
      val (pos, neg) = partitionMonomials(PMonomial)(Seq(), Seq())
      val p1 = ofMonomials(pos)
      val p2 = ofMonomials(neg)
      val prv0 = (this - p1 - p2).zeroTest.getOrElse(throw new RuntimeException("Runtime error in 0-proof for partitioning - this should never fail!"))
      val eqPrv = useDirectly(partition2,
        Seq(
          ("t_", lhs), ("r_", rhs),
          ("t1_", p1.lhs), ("r1_", p1.rhs),
          ("t2_", p2.lhs), ("r2_", p2.rhs),
        ),
        Seq(prv, p1.prv, p2.prv, prv0))
      (p1, p2, eqPrv)
    }

    def approx(prec: Int) : (ProvableSig, TreePolynomial, TreePolynomial) = this match {
      case Empty(_) =>
        (useDirectly(splitEmpty, Seq(("t_", lhs)), Seq(prv)), Empty(None), Empty(None))
      case Branch2(left, value, right, _) =>
        val (lPrv, l1, l2) = left.forgetPrv.approx(prec)
        val (rPrv, r1, r2) = right.forgetPrv.approx(prec)
        val (vPrv, v1, v2) = value.forgetPrv.approx(prec)
        (useDirectly(splitBranch2, Seq(("t_", lhs),
          ("l_", left.rhs), ("v_", value.rhs), ("r_", right.rhs),
          ("l1_", l1.rhs), ("v1_", v1.rhs), ("r1_", r1.rhs),
          ("l2_", l2.rhs), ("v2_", v2.rhs), ("r2_", r2.rhs)
        ), Seq(prv, lPrv, vPrv, rPrv)),
          Branch2(l1, v1, r1, None),
          Branch2(l2, v2, r2, None))
      case Branch3(left, value1, middle, value2, right, _) =>
        val (lPrv, l1, l2) = left.forgetPrv.approx(prec)
        val (v1Prv, v11, v12) = value1.forgetPrv.approx(prec)
        val (mPrv, m1, m2) = middle.forgetPrv.approx(prec)
        val (v2Prv, v21, v22) = value2.forgetPrv.approx(prec)
        val (rPrv, r1, r2) = right.forgetPrv.approx(prec)
        (useDirectly(splitBranch3, Seq(("t_", lhs),
          ("l_", left.rhs), ("v1_", value1.rhs), ("m_", middle.rhs), ("v2_", value2.rhs), ("r_", right.rhs),
          ("l1_", l1.rhs), ("v11_", v11.rhs), ("m1_", m1.rhs), ("v12_", v12.rhs), ("r1_", r1.rhs),
          ("l2_", l2.rhs), ("v21_", v21.rhs), ("m2_", m2.rhs), ("v22_", v22.rhs), ("r2_", r2.rhs)
        ), Seq(prv, lPrv, v1Prv, mPrv, v2Prv, rPrv)),
          Branch3(l1, v11, m1, v21, r1, None),
          Branch3(l2, v12, m2, v22, r2, None))
    }

    override def coefficient(powerProduct: PowerProduct): (BigDecimal, BigDecimal) = {
      lookup(powerProduct.sparse.toIndexedSeq) match {
        case None => (0, 1)
        case Some(v) => (v.coeff.num, v.coeff.denom)
      }
    }

    override def hornerForm(variableOrder: Option[List[Term]] = None) : ProvableSig  = {
      val vars = symbols(term)
      val ringsLib = new RingsLibrary(vars) // for non-certified computations @todo: initialize only once?!
      val ringVars = variableOrder.getOrElse(vars).map(ringsLib.toRing).toList
      val horner = ringsLib.toHorner(ringsLib.toRing(term), ringVars)
      equate(ofTerm(horner)).getOrElse(throw new RuntimeException("zeroTest failed for horner form - this should not happen!"))
    }

    override def divideAndRemainder(other: Polynomial, pretty: Boolean = false) : (Polynomial, Polynomial, ProvableSig) = {
      val rep1 = PolynomialArithV2Helpers.rhsOf(representation)
      val rep2 = PolynomialArithV2Helpers.rhsOf(other.representation)
      val ringsLibrary = new RingsLibrary(Traversable(rep1, rep2))
      val quotRem = ringsLibrary.ring.divideAndRemainder(ringsLibrary.toRing(rep1), ringsLibrary.toRing(rep2)).map { p =>
        val poly = ofTerm(ringsLibrary.fromRing(p))
        if (pretty) poly.prettyTerm else poly
      }
      val (quot, rem) = (quotRem(0), quotRem(1))
      equate(quot * other + rem) match {
        case Some(prv) => (quot, rem, prv)
        case None => throw new RuntimeException("unexpected failure: cannot prove polynomial division")
      }
    }

    def monomials : Seq[Monomial] = partitionMonomials(_ => true)(Seq(), Seq())._1
    override def variables : Set[Term] = monomials.foldLeft[Set[Term]](Set()){ case (vars, mon) => vars++mon.powerProduct.sparse.map(_._1) }

  }

  // invariants: sorted w.r.t. variable ordering, no zero exponents
  case class SparsePowerProduct(sparse : Seq[(Term, Int)]) extends PowerProduct {
    assert(sparse.map(_._1).sorted(variableOrdering) == sparse.map(_._1))
    assert(sparse.map(_._1).distinct == sparse.map(_._1))
    assert(sparse.forall(_._2 > 0))
    val degree = sparse.map(_._2).sum
  }
  def ofSparse(seq: Seq[(Term, Int)]) : SparsePowerProduct = {
    require(seq.forall(_._2 >= 0), "SparsePowerProduct: nonnegative exponents only")
    require(seq.map(_._1).distinct == seq.map(_._1), "SparsePowerProduct: variables must be unique")
    SparsePowerProduct(seq.filter(_._2 > 0).sortBy(_._1)(variableOrdering))
  }
  def ofSparse(powers: (Term, Int)*) : SparsePowerProduct = ofSparse(powers.toIndexedSeq)

  /** trust that wellformedness (wf) properties of [[SparsePowerProduct]] are maintained */
  private def wfPowerProduct(seq: Seq[(Term, Int)]) = SparsePowerProduct(seq)

  lazy val varPowerLemma = anyArgify(Ax.varPowerLemma.provable)
  lazy val varLemma = anyArgify(Ax.varLemma.provable)
  def Var(term: Term) : TreePolynomial =
    Branch2(Empty(None), Monomial(Coefficient(1, 1, None), wfPowerProduct(Seq((term, 1))), None), Empty(None),
      Some(varLemma(substAny("v_", term))))
  def Var(term: Term, power: Int) : TreePolynomial =
    Branch2(Empty(None), Monomial(Coefficient(1, 1, None), wfPowerProduct(Seq((term, power))), None), Empty(None),
      Some(useDirectly(varPowerLemma, Seq(("v_", term), ("n_", Number(power))), Seq())))

  lazy val constLemma = anyArgify(Ax.constLemma.provable)
  lazy val rationalLemma = anyArgify(Ax.rationalLemma.provable)
  def Const(num: BigDecimal, denom: BigDecimal) : TreePolynomial =
    Branch2(Empty(None), Monomial(Coefficient(num, denom, None), wfPowerProduct(Seq()), None), Empty(None),
      Some(useDirectly(rationalLemma, Seq(("n_", Number(num)), ("d_", Number(denom))), Seq())))
  def Const(num: BigDecimal) : TreePolynomial = Branch2(Empty(None), Monomial(Coefficient(num, 1, None), wfPowerProduct(IndexedSeq()), None), Empty(None),
    Some(constLemma(substAny("n_", Number(num)))))

  lazy val One : TreePolynomial = Const(1)

  case class Empty(prvO: Option[ProvableSig]) extends TreePolynomial {
    val defaultPrv = zez
    val prv = prvO.getOrElse(defaultPrv)
    override def forgetPrv = Empty(None)
    override def treeSketch: String = "."
    override def degree(include: Term => Boolean) = 0
    override def resetRepresentation(newRepresentation: ProvableSig): Polynomial = {
      require(rhsOf(newRepresentation)==rhsOf(prv))
      Empty(Some(newRepresentation))
    }
  }
  case class Branch2(left: TreePolynomial, value: Monomial, right: TreePolynomial, prvO: Option[ProvableSig]) extends TreePolynomial {
    lazy val defaultPrv = equalReflex(Seq(left.rhs, value.rhs, right.rhs).reduceLeft(Plus))
    // @note detour for "dependent" default argument
    val prv = prvO.getOrElse(defaultPrv)

    override def forgetPrv: TreePolynomial = Branch2(left, value, right, None)
    override def treeSketch: String = "[" + left.treeSketch + ", " + value.powersString + ", " + right.treeSketch + "]"
    override def degree(include: Term => Boolean) : Int =
      left.degree(include) max value.degree(include) max right.degree(include)
    override def resetRepresentation(newRepresentation: ProvableSig): Polynomial = {
      require(rhsOf(newRepresentation)==rhsOf(prv))
      Branch2(left, value, right, Some(newRepresentation))
    }
  }
  case class Branch3(left: TreePolynomial, value1: Monomial, mid: TreePolynomial, value2: Monomial, right: TreePolynomial, prvO: Option[ProvableSig]) extends TreePolynomial {
    lazy val defaultPrv = equalReflex(Seq(left.rhs, value1.rhs, mid.rhs, value2.rhs, right.rhs).reduceLeft(Plus))
    // @note detour for "dependent" default argument
    val prv = prvO.getOrElse(defaultPrv)

    override def forgetPrv: TreePolynomial = Branch3(left, value1, mid, value2, right, None)
    override def treeSketch: String = "{" + left.treeSketch + ", " + value1.powersString + ", " + mid.treeSketch + ", " + value2.powersString + ", " + right.treeSketch + "}"
    override def degree(include: Term => Boolean) : Int =
      left.degree(include) max value1.degree(include) max mid.degree(include) max value2.degree(include) max right.degree(include)
    override def resetRepresentation(newRepresentation: ProvableSig): Polynomial = {
      require(rhsOf(newRepresentation)==rhsOf(prv))
      Branch3(left, value1, mid, value2, right, Some(newRepresentation))
    }

  }

  def equate(t1: Term, t2: Term) : Option[ProvableSig] = ofTerm(t1).equate(ofTerm(t2))

  val equate: DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
    pos.checkTop
    pos.checkSucc
    seq.sub(pos) match {
      case Some(Equal(t1, t2)) =>
        PolynomialArithV2.reportBelleThrowables {
          equate(t1, t2)
        } match {
          case None => throw new TacticInapplicableFailure("Terms not equal (by equating coefficients): " + t1 + ", " + t2)
          case Some(prv) => cohideR(pos) & by(prv)
        }
      case Some(e) => throw new TacticInapplicableFailure("equate only applicable to equalities, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }
  }

  def normalize(term: Term) : ProvableSig = ofTerm(term).prettyRepresentation

  lazy private val eqNormalize = Ax.eqNormalize.provable
  val normalizeAt : DependentPositionTactic = anon { (pos: Position, seq: Sequent) =>
    seq.sub(pos) match {
      case Some(Equal(t, Number(n))) if n.compareTo(0) == 0 =>
        useAt(PolynomialArithV2.reportBelleThrowables{ normalize(t) }, PosInExpr(0::Nil))(pos ++ PosInExpr(0::Nil))
      case Some(Equal(s, t)) =>
        useAt(eqNormalize, PosInExpr(0::Nil))(pos) & normalizeAt(pos)
      case Some(t: Term) =>
        useAt(PolynomialArithV2.reportBelleThrowables{ normalize(t) }, PosInExpr(0::Nil))(pos)
      case Some(e) => throw new TacticInapplicableFailure("normalizeAt only applicable to equalities or terms, but got " + e.prettyString)
      case None => throw new IllFormedTacticApplicationException("Position " + pos + " does not point to a valid position in sequent " + seq.prettyString)
    }
  }

  lazy private val ratFormAdd = anyArgify(Ax.ratFormAdd.provable)
  lazy private val ratFormMinus = anyArgify(Ax.ratFormMinus.provable)
  lazy private val ratFormTimes = anyArgify(Ax.ratFormTimes.provable)
  lazy private val ratFormDivide = anyArgify(Ax.ratFormDivide.provable)
  lazy private val ratFormPower = anyArgify(Ax.ratFormPower.provable)
  lazy private val ratFormNeg = anyArgify(Ax.ratFormNeg.provable)

  lazy private val powerDivide0 = anyArgify(Ax.powerDivide0.provable)
  lazy private val powerDivideEven = anyArgify(Ax.powerDivideEven.provable)
  lazy private val powerDivideOdd = anyArgify(Ax.powerDivideOdd.provable)

  private def provePowerDivideLemma(n: Int, maxCache: Int, cache: Int=>ProvableSig) : ProvableSig = n match {
    case n if n <= maxCache => cache(n)
    case n if n > 0 && n % 2 == 0 =>
      val m = n / 2
      val mPrv = ProvableSig.proveArithmetic(BigDecimalQETool, Equal(Number(n), Times(Number(2), Number(m))))
      val powerDivideM = provePowerDivideLemma(m, maxCache, cache)
      useDirectly(powerDivideEven, Seq(("n_", Number(n)), ("m_", Number(m))), Seq(mPrv, powerDivideM))
    case n if n > 0 && n % 2 == 1 =>
      val m = n / 2
      val mPrv = ProvableSig.proveArithmetic(BigDecimalQETool, Equal(Number(n), Plus(Times(Number(2), Number(m)), Number(1))))
      val powerDivideM = provePowerDivideLemma(m, maxCache, cache)
      useDirectly(powerDivideOdd, Seq(("n_", Number(n)), ("m_", Number(m))), Seq(mPrv, powerDivideM))
    case _ =>
      throw new IllegalArgumentException("powerDivideLemma requires natural number exponent")
  }
  private val powerDivideLemmas = (0 to 100).map(provePowerDivideLemma(_, 0, i => powerDivide0)).toArray
  /** lookup or prove lemma of the form "(x_(||) / y_(||))^i = x_(||)^i / y_(||)^i " */
  def powerDivideLemma(i: Int) = if (i <= 100) powerDivideLemmas(i) else provePowerDivideLemma(i, 100, powerDivideLemmas)

  def ratForm(term: Term): (Polynomial, Polynomial, ProvableSig) = {
    lazy val ringsLibrary = new RingsLibrary(Seq(term))

    def gcdAndRemainders(a: ringsLibrary.Ring, b: ringsLibrary.Ring): (ringsLibrary.Ring, ringsLibrary.Ring, ringsLibrary.Ring) = {
      import ringsLibrary._
      val gcd = ring.gcd(a, b)
      val ra = ring.divideExact(a, gcd)
      val rb = ring.divideExact(b, gcd)
      (gcd, ra, rb)
    }

    def rec(term: Term): (Polynomial, ringsLibrary.Ring, Polynomial, ringsLibrary.Ring, ProvableSig) = term match {
      case binop: BinaryCompositeTerm =>
        val (nx, nxR, dx, dxR, xPrv) = rec(binop.left)
        val (ny, nyR, dy, dyR, yPrv) = rec(binop.right)
        binop match {
          case Plus(_, _) | Minus(_, _) =>
            val (ratFormLemma, polyOp, ringOp) = binop match {
              case Plus(_, _) =>
                (ratFormAdd,
                  (p1: Polynomial, p2: Polynomial) => p1 + p2,
                  (p1: ringsLibrary.Ring, p2: ringsLibrary.Ring) => p1.add(p2))
              case Minus(_, _) =>
                (ratFormMinus,
                  (p1: Polynomial, p2: Polynomial) => p1 - p2,
                  (p1: ringsLibrary.Ring, p2: ringsLibrary.Ring) => p1.subtract(p2))
            }
            val (gcdR, rxR, ryR) = gcdAndRemainders(dxR, dyR)
            val gcd = ringsLibrary.fromRing(gcdR)
            val gcdP = ofTerm(gcd)
            val rx = ringsLibrary.fromRing(rxR)
            val ry = ringsLibrary.fromRing(ryR)
            val rxP = ofTerm(rx)
            val ryP = ofTerm(ry)
            val nz = polyOp(nx * ryP, ny * rxP)
            val nzR = ringOp(nxR.multiply(ryR), nyR.multiply(rxR))
            val dz = rxP * gcdP * ryP
            val dzR = dxR.multiply(ryR)
            val dx = gcdP * rxP
            val dy = gcdP * ryP
            val prv = useDirectly(ratFormLemma,
              Seq(("x_", binop.left), ("nx_", nx.term), ("dx_", rhsOf(dx.representation)),
                ("y_", binop.right), ("ny_", ny.term), ("dy_", rhsOf(dy.representation)),
                ("gcd_", gcd),
                ("rx_", rx),
                ("ry_", ry),
                ("nz_", rhsOf(nz.representation)),
                ("dz_", rhsOf(dz.representation))
              ),
              Seq(
                xPrv,
                yPrv,
                dx.representation,
                dy.representation,
                nz.representation,
                dz.representation
              ))
            (nz.resetTerm, nzR, dz.resetTerm, dzR, prv)
          case Times(_, _) =>
            val (nz, nzR) = (nx * ny, nxR.multiply(nyR))
            val (dz, dzR) = (dx * dy, dxR.multiply(dyR))
            val prv = useDirectly(ratFormTimes,
              Seq(("x_", binop.left), ("nx_", nx.term), ("dx_", dx.term),
                ("y_", binop.right), ("ny_", ny.term), ("dy_", dy.term),
                ("nz_", rhsOf(nz.representation)),
                ("dz_", rhsOf(dz.representation))
              ),
              Seq(
                xPrv,
                yPrv,
                nz.representation,
                dz.representation
              ))
            (nz.resetTerm, nzR, dz.resetTerm, dzR, prv)
          case Divide(_, _) =>
            val (nz, nzR) = (nx * dy, nxR.multiply(dyR))
            val (dz, dzR) = (ny * dx, nyR.multiply(dxR))
            val prv = useDirectly(ratFormDivide,
              Seq(("x_", binop.left), ("nx_", nx.term), ("dx_", dx.term),
                ("y_", binop.right), ("ny_", ny.term), ("dy_", dy.term),
                ("nz_", rhsOf(nz.representation)),
                ("dz_", rhsOf(dz.representation))
              ),
              Seq(
                xPrv,
                yPrv,
                nz.representation,
                dz.representation
              ))
            (nz.resetTerm, nzR, dz.resetTerm, dzR, prv)
          case Power(_, _) =>
            if (dyR.isOne && nyR.isConstant) {
              val (mNum, mDenom) = ny.coefficient(SparsePowerProduct(Seq()))
              val m = (mNum / mDenom).toIntExact
              val ymPrv = (ny / dy).equate(m).getOrElse(throw new RuntimeException("expected to prove that polynomial equals integer"))
              val powerDividePrv = useDirectly(powerDivideLemma(m), Seq(("x_", nx.term), ("y_", dx.term)), Seq())
              val (nz, nzR) = (nx ^ m, ringsLibrary.ring.pow(nxR, m))
              val (dz, dzR) = (dx ^ m, ringsLibrary.ring.pow(dxR, m))
              val prv = useDirectly(ratFormPower,
                Seq(("x_", binop.left), ("nx_", nx.term), ("dx_", dx.term),
                  ("y_", binop.right), ("ny_", ny.term), ("dy_", dy.term),
                  ("m_", Number(m)),
                  ("nz_", rhsOf(nz.representation)),
                  ("dz_", rhsOf(dz.representation))
                ),
                Seq(
                  xPrv,
                  yPrv,
                  ymPrv,
                  powerDividePrv,
                  nz.representation,
                  dz.representation
                ))
              (nz.resetTerm, nzR, dz.resetTerm, dzR, prv)
            } else throw NonSupportedExponentException("exponent does not normalize to a natural number: " + ny + "/" + dy)
        }
      case Neg(c) =>
        val (nx, nxR, dx, dxR, xPrv) = rec(c)
        val (nz, nzR) = (-nx, nxR.negate)
        val prv = useDirectly(ratFormNeg,
          Seq(("x_", c), ("nx_", nx.term), ("dx_", dx.term),
            ("nz_", rhsOf(nz.representation))
          ),
          Seq(
            xPrv,
            nz.representation
          ))
        (nz.resetTerm, nzR, dx.resetTerm, dxR, prv)
      case a: AtomicTerm =>
        val aP = ofTerm(a)
        (aP.resetTerm, ringsLibrary.toRing(a), 1.resetTerm, ringsLibrary.ring.getOne,
          useDirectly(divideIdentity,
            Seq(
              ("x_", a),
              ("y_", rhsOf(aP.representation)),
              ("z_", rhsOf(1.representation))
            ), Seq(aP.representation, 1.representation)))
      case _ =>
        throw NonPolynomialArithmeticException("Operation not supported by polynomial arithmetic: " + term)
    }

    val (n, _, d, _, prv) = rec(term)
    val prettyPrv0 = useFor(n.prettyRepresentation, PosInExpr(0::Nil))(Position(1, 1::0::Nil))(prv)
    val prettyPrv = useFor(d.prettyRepresentation, PosInExpr(0::Nil))(Position(1, 1::1::Nil))(prettyPrv0)
    (n.prettyTerm, d.prettyTerm, prettyPrv)
  }

}
