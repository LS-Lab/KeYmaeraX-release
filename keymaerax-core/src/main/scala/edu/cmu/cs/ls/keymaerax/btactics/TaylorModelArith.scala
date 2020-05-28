package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TaylorModelTactics.TaylorModel
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ext.{BigDecimalTool, RingsLibrary}
import edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool

import scala.collection.immutable._

trait TaylorModelOptions {
  val precision: Integer
  val order: Integer
}

/**
  * Taylor model arithmetic
  *
  * Here, a Taylor model is a data structure maintaining a proof that some term is element of the Taylor model.
  *
  * */
class TaylorModelArith { // @note a class and not an object in order to initialize everything when constructing the class (@derive could help)
  val polynomialRing = PolynomialArithV2.ring

  import polynomialRing._
  import PolynomialArithV2Helpers._

  private def tmFormula(elem: Term, poly: Term, lower: Term, upper: Term) = {
    val err = BaseVariable("err_")
    Exists(Seq(err),
      And(Equal(elem, Plus(poly, err)),
        And(LessEqual(lower, err),
          LessEqual(err, upper)
        ))
    )
  }

  private def weakenWith(context: IndexedSeq[Formula], prv: ProvableSig) : ProvableSig = {
    assert(prv.conclusion.ante.isEmpty)
    ProvableSig.startProof(Sequent(context, prv.conclusion.succ)).apply(CoHideRight(SuccPos(0)), 0).apply(prv, 0)
  }

  private val plusPrv = AnonymousLemmas.remember(
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "(\\exists err_ (elem2_() = poly2_() + err_ & l2_() <= err_ & err_ <= u2_())) &" +
      "poly1_() + poly2_() = poly_() &" +
      "(\\forall i1_ \\forall i2_ (l1_() <= i1_ & i1_ <= u1_() & l2_() <= i2_ & i2_ <= u2_() ->" +
      "  (l_() <= i1_ + i2_ & i1_ + i2_ <= u_())))" +
      ") ->" +
      "\\exists err_ (elem1_() + elem2_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula, QE & done)

  private val minusPrv = AnonymousLemmas.remember(
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "(\\exists err_ (elem2_() = poly2_() + err_ & l2_() <= err_ & err_ <= u2_())) &" +
      "poly1_() - poly2_() = poly_() &" +
      "(\\forall i1_ \\forall i2_ (l1_() <= i1_ & i1_ <= u1_() & l2_() <= i2_ & i2_ <= u2_() ->" +
      "  (l_() <= i1_ - i2_ & i1_ - i2_ <= u_())))" +
      ") ->" +
      "\\exists err_ (elem1_() - elem2_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula, QE & done)

  private val collectPrv = AnonymousLemmas.remember(
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "poly1_() = polyLow_() + polyHigh_() &" +
      "polyLow_() = poly_() &" +
      "polyHigh_() = rem_() & " +
      "(\\forall i1_ (l1_() <= i1_ & i1_ <= u1_() ->" +
      "  (l_() <= rem_() + i1_ & rem_() + i1_  <= u_())))" +
      ") ->" +
      "\\exists err_ (elem1_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    QE & done
  )

  private val intervalPrv = AnonymousLemmas.remember(
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "poly1_() = rem_() &" +
      "(\\forall i1_ (l1_() <= i1_ & i1_ <= u1_() ->" +
      "  (l_() <= rem_() + i1_ & rem_() + i1_  <= u_())))" +
      ") ->" +
      "l_() <= elem1_() & elem1_() <= u_()").asFormula,
    QE & done
  )

  private val timesPrv = AnonymousLemmas.remember(
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "(\\exists err_ (elem2_() = poly2_() + err_ & l2_() <= err_ & err_ <= u2_())) &" +
      "poly1_() * poly2_() = polyLow_() + polyHigh_() &" +
      "polyLow_() = poly_() &" +
      "polyHigh_() = rem_() & " +
      "(\\forall i1_ \\forall i2_ (l1_() <= i1_ & i1_ <= u1_() & l2_() <= i2_ & i2_ <= u2_() ->" +
      "  (l_() <= rem_() + i1_ * poly2_() + i2_ * poly1_() + i1_ * i2_ & rem_() + i1_ * poly2_() + i2_ * poly1_() + i1_ * i2_ <= u_())))" + // @todo: horner form for poly1, poly2 ?!
      ") ->" +
      "\\exists err_ (elem1_() * elem2_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    implyR(1) & andL(-1) & andL(-2) & andL(-3) & andL(-4) & andL(-5) & existsL(-1) & existsL(-1) & allL("err__0".asTerm)(-4) & allL("err_".asTerm)(-4) &
      existsR("rem_() + err__0 * poly2_() + err_ * poly1_() + err__0 * err_".asTerm)(1) & QE & done
  )

  private val squarePrv = AnonymousLemmas.remember(//@todo: is there a better scheme than just multiplication?
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "poly1_()^2 = polyLow_() + polyHigh_() &" +
      "polyLow_() = poly_() &" +
      "polyHigh_() = rem_() & " +
      "(\\forall i1_ (l1_() <= i1_ & i1_ <= u1_() ->" +
      "  (l_() <= rem_() + 2 * i1_ * poly1_() + i1_^2 & rem_() + 2 * i1_ * poly1_() + i1_^2 <= u_())))" + // @todo: horner form for poly1 ?!
      ") ->" +
      "\\exists err_ (elem1_()^2 = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    implyR(1) & andL(-1) & andL(-2) & andL(-3) & andL(-4) & existsL(-1) & allL("err_".asTerm)(-4) &
      existsR("rem_() + 2 * err_ * poly1_() + err_^2".asTerm)(1) & QE & done
  )

  private val powerOne = AnonymousLemmas.remember((
    "(\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_()))" +
    " ->" +
    "\\exists err_ (elem1_()^1 = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())").asFormula, QE & done)

  private val powerEven = AnonymousLemmas.remember((
    "((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "(\\exists err_ ((elem1_()^m_())^2 = poly_() + err_ & l_() <= err_ & err_ <= u_())) &" +
      "(n_() = 2*m_() <-> true)" +
      ")" +
      "->" +
      "\\exists err_ (elem1_()^n_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    implyR(1) & andL(-1) & andL(-2) & cut("(elem1_()^m_())^2 = elem1_()^(2*m_())".asFormula) & Idioms.<(
      eqL2R(-4)(-2) & hideL(-4) & useAt(Ax.equivTrue, PosInExpr(0 :: Nil))(-3) & eqR2L(-3)(-2) & QE & done,
      cohideR(2) & QE & done
    )
  )

  private val powerOdd = AnonymousLemmas.remember((
    "((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "(\\exists err_ ((elem1_()^m_())^2*elem1_() = poly_() + err_ & l_() <= err_ & err_ <= u_())) &" +
      "(n_() = 2*m_() + 1 <-> true)" +
      ")" +
      "->" +
      "\\exists err_ (elem1_()^n_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    implyR(1) & andL(-1) & andL(-2) & cut("(elem1_()^m_())^2*elem1_() = elem1_()^(2*m_() + 1)".asFormula) & Idioms.<(
      eqL2R(-4)(-2) & hideL(-4) & useAt(Ax.equivTrue, PosInExpr(0 :: Nil))(-3) & eqR2L(-3)(-2) & QE & done,
      cohideR(2) & QE & done
    )
  )

  private val negPrv = AnonymousLemmas.remember(
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "-poly1_() = poly_() &" +
      "(\\forall i1_ (l1_() <= i1_ & i1_ <= u1_() ->" +
      "  (l_() <= -i1_ & -i1_ <= u_())))" +
      ") ->" +
      "\\exists err_ (-elem1_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula, QE & done)

  private val exactPrv = AnonymousLemmas.remember(
    ("elem_() = poly_() ->" +
      "\\exists err_ (elem_() = poly_() + err_ & 0 <= err_ & err_ <= 0)").asFormula, QE & done
  )

  private val approxPrv = AnonymousLemmas.remember(
    ("(" +
      "\\exists err_ (elem_() = poly_() + err_ & l_() <= err_ & err_ <= u_()) &" +
      "poly_() = poly1_() + poly2_() &" +
      "poly1_() = poly1rep_() &" +
      "poly2_() = poly2rep_() &" +
      "(\\forall i1_ (l_() <= i1_ & i1_ <= u_() ->" +
      "   l2_() <= poly2rep_() + i1_ & poly2rep_() + i1_ <= u2_()))" +
      ") ->" +
      "\\exists err_ (elem_() = poly1rep_() + err_ & l2_() <= err_ & err_ <= u2_())").asFormula,
    QE & done
  )

  // proof of "poly.term = horner form"
  // TODO: add to PolynomialLibrary
  def toHorner(poly: Polynomial) : ProvableSig  = {
    val vars = symbols(poly.term)
    val ringsLib = new RingsLibrary(vars) // for non-certified computations @todo: initialize only once?!
    val ringVars = vars.map(ringsLib.toRing).toList
    val horner = ringsLib.toHorner(ringsLib.toRing(poly.term), ringVars)
    poly.equate(ofTerm(horner)).getOrElse(throw new RuntimeException("zeroTest failed for horner form - this should not happen!"))
  }

  /**
    * data structure with certifying computations
    * maintains the invariant
    *   prv: \exists err. elem = poly + err & err \in [lower; upper]
    *
    * */
  case class TM(elem: Term, poly: Polynomial, lower: Term, upper: Term, prv: ProvableSig) {
    val context = prv.conclusion.ante
    assert(prv.conclusion.succ(0) == tmFormula(elem, rhsOf(poly.representation), lower, upper))
    def checkCompatibleContext(other: TM) =
      if (context != other.context) throw new IllegalArgumentException("Incompatible contexts: " + context + " and " + other.context)

    /** exact addition */
    def +!(other: TM)(implicit options: TaylorModelOptions) : TM = {
      checkCompatibleContext(other)
      val newPoly = poly.resetTerm + other.poly.resetTerm

      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveBinop(new BigDecimalTool)(options.precision)(IndexedSeq())(Plus)(lower, upper)(other.lower, other.upper)
      val newPrv = useDirectlyConst(weakenWith(context, plusPrv.fact), Seq(
        ("elem1_", elem),
        ("poly1_", rhsOf(poly.representation)),
        ("l1_", lower),
        ("u1_", upper),
        ("elem2_", other.elem),
        ("poly2_", rhsOf(other.poly.representation)),
        ("l2_", other.lower),
        ("u2_", other.upper),
        ("poly_", rhsOf(newPoly.representation)),
        ("l_", l),
        ("u_", u)
      ), Seq(prv, other.prv, weakenWith(context, newPoly.representation), weakenWith(context, newIvlPrv)))
      TM(Plus(elem, other.elem), (poly + other.poly).resetTerm, l, u, newPrv)
    }

    /** approximate addition */
    def +(other: TM)(implicit options: TaylorModelOptions) : TM = (this +! other).approx

    /** exact subtraction */
    def -!(other: TM)(implicit options: TaylorModelOptions) : TM = {
      checkCompatibleContext(other)
      val newPoly = poly.resetTerm - other.poly.resetTerm

      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveBinop(new BigDecimalTool)(options.precision)(IndexedSeq())(Minus)(lower, upper)(other.lower, other.upper)
      val newPrv = useDirectlyConst(weakenWith(context, minusPrv.fact), Seq(
        ("elem1_", elem),
        ("poly1_", rhsOf(poly.representation)),
        ("l1_", lower),
        ("u1_", upper),
        ("elem2_", other.elem),
        ("poly2_", rhsOf(other.poly.representation)),
        ("l2_", other.lower),
        ("u2_", other.upper),
        ("poly_", rhsOf(newPoly.representation)),
        ("l_", l),
        ("u_", u)
      ), Seq(prv, other.prv, weakenWith(context, newPoly.representation), weakenWith(context, newIvlPrv)))
      TM(Minus(elem, other.elem), (poly - other.poly).resetTerm, l, u, newPrv)
    }
    /** approximate subtraction */
    def -(other: TM)(implicit options: TaylorModelOptions) : TM = (this -!other).approx

    def collectHigherOrderTerms(implicit options: TaylorModelOptions) : TM = {
      val (polyLow, polyHigh, partitionPrv) = poly.resetTerm.partition{case (n, d, powers) => powers.map(_._2).sum <= options.order}
      val hornerPrv = toHorner(polyHigh)
      val rem = rhsOf(hornerPrv)
      val poly1 = rhsOf(poly.representation)
      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(options.precision)(context)(i => Plus(rem, i))(lower, upper)
      val newPrv = useDirectlyConst(weakenWith(context, collectPrv.fact), Seq(
        ("elem1_", elem),
        ("poly1_", poly1),
        ("l1_", lower),
        ("u1_", upper),

        ("polyLow_", polyLow.term),
        ("poly_", rhsOf(polyLow.representation)),
        ("polyHigh_", polyHigh.term),
        ("rem_", rem),
        ("l_", l),
        ("u_", u)
      ), Seq(prv,
        weakenWith(context, partitionPrv),
        weakenWith(context, polyLow.representation),
        weakenWith(context, hornerPrv),
        newIvlPrv))
      TM(elem, polyLow.resetTerm, l, u, newPrv)
    }

    /** prove interval enclosure of Taylor model */
    def interval(implicit options: TaylorModelOptions) : ProvableSig = {
      val hornerPrv = toHorner(poly)
      val rem = rhsOf(hornerPrv)
      val poly1 = rhsOf(poly.representation)
      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(options.precision)(context)(i => Plus(rem, i))(lower, upper)
      useDirectlyConst(weakenWith(context, intervalPrv.fact), Seq(
        ("elem1_", elem),
        ("poly1_", poly1),
        ("l1_", lower),
        ("u1_", upper),

        ("rem_", rem),
        ("l_", l),
        ("u_", u)
      ), Seq(prv,
        weakenWith(context, hornerPrv),
        newIvlPrv))
    }

    /** exact multiplication */
    def *!(other: TM)(implicit options: TaylorModelOptions) : TM = {
      checkCompatibleContext(other)
      val (polyLow, polyHigh, partitionPrv) = (poly.resetTerm * other.poly.resetTerm).partition{case (n, d, powers) => powers.map(_._2).sum <= options.order}

      val hornerPrv = toHorner(polyHigh)
      val rem = rhsOf(hornerPrv)
      val poly1 = rhsOf(poly.representation)
      val poly2 = rhsOf(other.poly.representation)
      def intervalBounds(i1: Term, i2: Term) : Term = Seq(rem, Times(i1, poly2), Times(i2, poly1), Times(i1, i2)).reduceLeft(Plus)
      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveBinop(new BigDecimalTool)(options.precision)(context)(intervalBounds)(lower, upper)(other.lower, other.upper)
      val newPrv = useDirectlyConst(weakenWith(context, timesPrv.fact), Seq(
        ("elem1_", elem),
        ("poly1_", poly1),
        ("l1_", lower),
        ("u1_", upper),
        ("elem2_", other.elem),
        ("poly2_", poly2),
        ("l2_", other.lower),
        ("u2_", other.upper),

        ("polyLow_", polyLow.term),
        ("poly_", rhsOf(polyLow.representation)),
        ("polyHigh_", polyHigh.term),
        ("rem_", rem),
        ("l_", l),
        ("u_", u)
      ), Seq(prv, other.prv,
        weakenWith(context, partitionPrv),
        weakenWith(context, polyLow.representation),
        weakenWith(context, hornerPrv),
        newIvlPrv))
      TM(Times(elem, other.elem), polyLow.resetTerm, l, u, newPrv)
    }
    /** approximate multiplication */
    def *(other: TM)(implicit options: TaylorModelOptions) : TM = (this *! other).approx

    /** exact negation */
    def unary_-(implicit options: TaylorModelOptions) : TM = {
      val newPoly = -(poly.resetTerm)

      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(options.precision)(IndexedSeq())(Neg)(lower, upper)
      val newPrv = useDirectlyConst(weakenWith(context, negPrv.fact), Seq(
        ("elem1_", elem),
        ("poly1_", rhsOf(poly.representation)),
        ("l1_", lower),
        ("u1_", upper),
        ("poly_", rhsOf(newPoly.representation)),
        ("l_", l),
        ("u_", u)
      ), Seq(prv, weakenWith(context, newPoly.representation), weakenWith(context, newIvlPrv)))
      TM(Neg(elem), (-poly).resetTerm, l, u, newPrv)
    }

    /** exact square */
    def squareExact(implicit options: TaylorModelOptions) : TM = {
      val (polyLow, polyHigh, partitionPrv) = (poly.resetTerm^2).partition{case (n, d, powers) => powers.map(_._2).sum <= options.order}
      val hornerPrv = toHorner(polyHigh)
      val rem = rhsOf(hornerPrv)
      val poly1 = rhsOf(poly.representation)
      def intervalBounds(i1: Term) : Term = Seq(rem, Times(Times(Number(2), i1), poly1), Power(i1, Number(2))).reduceLeft(Plus)
      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(options.precision)(context)(intervalBounds)(lower, upper)
      val newPrv = useDirectlyConst(weakenWith(context, squarePrv.fact), Seq(
        ("elem1_", elem),
        ("poly1_", poly1),
        ("l1_", lower),
        ("u1_", upper),
        ("polyLow_", polyLow.term),
        ("polyHigh_", polyHigh.term),
        ("rem_", rem),
        ("poly_", rhsOf(polyLow.representation)),
        ("l_", l),
        ("u_", u)
      ), Seq(prv, weakenWith(context, partitionPrv),
        weakenWith(context, polyLow.representation),
        weakenWith(context, hornerPrv),
        newIvlPrv))
      TM(Power(elem, Number(2)), (polyLow).resetTerm, l, u, newPrv)
    }
    /** approximate square */
    def square(implicit options: TaylorModelOptions) : TM = this.squareExact.approx

    /** approximate exponentiation */
    def ^(n: Int)(implicit options: TaylorModelOptions) : TM = n match {
      case 1 =>
        val newPrv = useDirectlyConst(weakenWith(context, powerOne.fact), Seq(
          ("elem1_", elem),
          ("poly1_", rhsOf(poly.representation)),
          ("l1_", lower),
          ("u1_", upper)),
          Seq(prv))
        TM(Power(elem, Number(1)), poly.resetTerm, lower, upper, newPrv)
      case n if n>0 && n%2 == 0 =>
        val m = n / 2
        val mPrv = ProvableSig.proveArithmetic(BigDecimalQETool, Equal(Number(n), Times(Number(2), Number(m))))
        val p = (this ^ m).square(options)
        val newPrv =
          useDirectlyConst(weakenWith(context, powerEven.fact), Seq(
            ("elem1_", elem),
            ("poly1_", rhsOf(poly.representation)),
            ("l1_", lower),
            ("u1_", upper),
            ("m_", Number(m)),
            ("n_", Number(n)),
            ("l_", p.lower),
            ("u_", p.upper),
            ("poly_", rhsOf(p.poly.representation))
          ),
            Seq(prv, p.prv, weakenWith(context, mPrv)))
        TM(Power(elem, Number(n)), p.poly.resetTerm, p.lower, p.upper, newPrv)
      case n if n>0 =>
        val m = n / 2
        val mPrv = ProvableSig.proveArithmetic(BigDecimalQETool, Equal(Number(n), Plus(Times(Number(2), Number(m)), Number(1))))
        val p = (this ^ m).square * this
        val newPrv =
          useDirectlyConst(weakenWith(context, powerOdd.fact), Seq(
            ("elem1_", elem),
            ("poly1_", rhsOf(poly.representation)),
            ("l1_", lower),
            ("u1_", upper),
            ("m_", Number(m)),
            ("n_", Number(n)),
            ("l_", p.lower),
            ("u_", p.upper),
            ("poly_", rhsOf(p.poly.representation))
          ),
            Seq(prv, p.prv, weakenWith(context, mPrv)))
        TM(Power(elem, Number(n)), p.poly.resetTerm, p.lower, p.upper, newPrv)
      case _ => throw new IllegalArgumentException("Taylor model ^ n requires n > 0, not n = " + n)
    }

    /** round coefficients of polynomial part, incorporate error in interval */
    def approx(implicit options: TaylorModelOptions) : TM = {
      val (polyApproxPrv, poly1, poly2) = poly.approx(options.precision)
      val poly1rep = rhsOf(poly1.representation)
      val poly2repPrv = toHorner(poly2)
      val poly2rep = rhsOf(poly2repPrv)
      val (ivlPrv, l2, u2) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(options.precision)(context)(i1 => Plus(poly2rep, i1))(lower, upper)
      val newPrv = useDirectlyConst(weakenWith(context, approxPrv.fact),
        Seq(
          ("elem_", elem),
          ("poly_", rhsOf(poly.representation)),
          ("l_", lower),
          ("u_", upper),
          ("poly1_", poly1.term),
          ("poly1rep_", poly1rep),
          ("poly2_", poly2.term),
          ("poly2rep_", poly2rep),
          ("l2_", l2),
          ("u2_", u2)
        ),
        Seq(prv, weakenWith(context, polyApproxPrv), weakenWith(context, poly1.representation), weakenWith(context, poly2repPrv), ivlPrv)
      )
      TM(elem, poly1.resetTerm, l2, u2, newPrv)
    }

    /** theorem with a "prettier" representation of the certificate */
    def prettyPrv(implicit options: TaylorModelOptions): ProvableSig = {
      val (l1, l2) = IntervalArithmeticV2.eval_ivl(options.precision)(HashMap(), HashMap())(lower)
      val (u1, u2) = IntervalArithmeticV2.eval_ivl(options.precision)(HashMap(), HashMap())(upper)
      val prettyLower = if (l1 == l2) Number(l1) else lower
      val prettyUpper = if (u1 == u2) Number(u1) else upper
      proveBy(ProvableSig.startProof(Sequent(context, IndexedSeq(tmFormula(elem, rhsOf(poly.prettyRepresentation),
        prettyLower, prettyUpper)))).apply(CutRight(prv.conclusion.succ(0), SuccPos(0)), 0).
        apply(CoHideRight(SuccPos(0)), 1).
        apply(ImplyRight(SuccPos(0)), 1),
        Idioms.<(
          by(prv),
          existsL(-1) & existsR("err_".asTerm)(1) & andL(-1) & andL(-2) & andR(1) &
          Idioms.<(
            cohideOnlyL(-1) &
              useAt(poly.prettyRepresentation, PosInExpr(1::Nil))(1, 1::0::Nil) & closeId
            ,
            hideL(-1) & IntervalArithmeticV2.intervalArithmeticBool(options.precision, new BigDecimalTool)(1)
          )
        )
      )
    }
  }

  /** constructs a Taylor model by proving the required certificate with a tactic */
  def TM(elem: Term, poly: Polynomial, lower: Term, upper: Term, context: IndexedSeq[Formula], be: BelleExpr): TM = {
    TM(elem, poly, lower, upper,
      proveBy(Sequent(context, IndexedSeq(tmFormula(elem, rhsOf(poly.representation), lower, upper))), be & done))
  }

  /** constructs a Taylor model with zero interval part */
  def Exact(elem: Polynomial, context: IndexedSeq[Formula]): TM = {
    val newPrv = useDirectlyConst(weakenWith(context, exactPrv.fact),
      Seq(("elem_", elem.term), ("poly_", rhsOf(elem.representation))),
      Seq(weakenWith(context, elem.representation))
    )
    TM(elem.term, elem.resetTerm, Number(0), Number(0), newPrv)
  }

}
