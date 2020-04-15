package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.btactics.PolynomialArithV2._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ext.{BigDecimalTool, RingsLibrary}
import edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool

import scala.collection.immutable._


class TaylorModelArith(context: IndexedSeq[Formula],
                       vars: IndexedSeq[Term],
                       prec: Int,
                       order: Int
                      ) {
  val polynomialRing = PolynomialArithV2.PolynomialRing(vars)
  val ringsLib = new RingsLibrary(vars) // for non-certified computations

  import polynomialRing._
  import PolynomialArithV2Helpers._

  def tmFormula(elem: Term, poly: Polynomial, lower: Term, upper: Term) = {
    val err = BaseVariable("err_")
    Exists(Seq(err),
      And(Equal(elem, Plus(rhsOf(poly.representation), err)),
        And(LessEqual(lower, err),
          LessEqual(err, upper)
        ))
    )
  }

  def weakenWithContext(prv: ProvableSig) = {
    assert(prv.conclusion.ante.isEmpty)
    ProvableSig.startProof(Sequent(context, prv.conclusion.succ)).apply(CoHideRight(SuccPos(0)), 0).apply(prv, 0)
  }

  val eqMinusI = rememberAny("(t_() - s_() = 0) -> t_() = s_()".asFormula, QE & done)

  val plusPrv = AnonymousLemmas.remember(
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "(\\exists err_ (elem2_() = poly2_() + err_ & l2_() <= err_ & err_ <= u2_())) &" +
      "poly1_() + poly2_() = poly_() &" +
      "(\\forall i1_ \\forall i2_ (l1_() <= i1_ & i1_ <= u1_() & l2_() <= i2_ & i2_ <= u2_() ->" +
      "  (l_() <= i1_ + i2_ & i1_ + i2_ <= u_())))" +
      ") ->" +
      "\\exists err_ (elem1_() + elem2_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula, QE & done)

  val minusPrv = AnonymousLemmas.remember(
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "(\\exists err_ (elem2_() = poly2_() + err_ & l2_() <= err_ & err_ <= u2_())) &" +
      "poly1_() - poly2_() = poly_() &" +
      "(\\forall i1_ \\forall i2_ (l1_() <= i1_ & i1_ <= u1_() & l2_() <= i2_ & i2_ <= u2_() ->" +
      "  (l_() <= i1_ - i2_ & i1_ - i2_ <= u_())))" +
      ") ->" +
      "\\exists err_ (elem1_() - elem2_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula, QE & done)

  val timesPrv = AnonymousLemmas.remember(
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

  val squarePrv = AnonymousLemmas.remember(//@todo: is there a better scheme than just multiplication?
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
  val powerOne = AnonymousLemmas.remember((
    "(\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_()))" +
    " ->" +
    "\\exists err_ (elem1_()^1 = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())").asFormula, QE & done)

  val powerEven = AnonymousLemmas.remember((
    "((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "(\\exists err_ ((elem1_()^m_())^2 = poly_() + err_ & l_() <= err_ & err_ <= u_())) &" +
      "(n_() = 2*m_() <-> true)" +
      ")" +
      "->" +
      "\\exists err_ (elem1_()^n_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    implyR(1) & andL(-1) & andL(-2) & cut("(elem1_()^m_())^2 = elem1_()^(2*m_())".asFormula) & Idioms.<(
      eqL2R(-4)(-2) & hideL(-4) & useAt(DerivedAxioms.equivTrue, PosInExpr(0 :: Nil))(-3) & eqR2L(-3)(-2) & QE & done,
      cohideR(2) & QE & done
    )
  )

  val powerOdd = AnonymousLemmas.remember((
    "((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "(\\exists err_ ((elem1_()^m_())^2*elem1_() = poly_() + err_ & l_() <= err_ & err_ <= u_())) &" +
      "(n_() = 2*m_() + 1 <-> true)" +
      ")" +
      "->" +
      "\\exists err_ (elem1_()^n_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula,
    implyR(1) & andL(-1) & andL(-2) & cut("(elem1_()^m_())^2*elem1_() = elem1_()^(2*m_() + 1)".asFormula) & Idioms.<(
      eqL2R(-4)(-2) & hideL(-4) & useAt(DerivedAxioms.equivTrue, PosInExpr(0 :: Nil))(-3) & eqR2L(-3)(-2) & QE & done,
      cohideR(2) & QE & done
    )
  )

  val negPrv = AnonymousLemmas.remember(
    ("((\\exists err_ (elem1_() = poly1_() + err_ & l1_() <= err_ & err_ <= u1_())) &" +
      "-poly1_() = poly_() &" +
      "(\\forall i1_ (l1_() <= i1_ & i1_ <= u1_() ->" +
      "  (l_() <= -i1_ & -i1_ <= u_())))" +
      ") ->" +
      "\\exists err_ (-elem1_() = poly_() + err_ & l_() <= err_ & err_ <= u_())").asFormula, QE & done)

  val exactPrv = AnonymousLemmas.remember(
    ("elem_() = poly_() ->" +
      "\\exists err_ (elem_() = poly_() + err_ & 0 <= err_ & err_ <= 0)").asFormula, QE & done
  )

  val approxPrv = AnonymousLemmas.remember(
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

  val ringVars = vars.map(ringsLib.toRing).toList
  // proof of "poly.term = horner form"
  // TODO: add to PolynomialLibrary
  def toHorner(poly: Polynomial) : ProvableSig  = {
    val horner = ringsLib.toHorner(ringsLib.toRing(poly.term), ringVars)
    val zeroPrv = (poly - ofTerm(horner)).zeroTest.getOrElse(throw new RuntimeException("zeroTest failed for horner form - this should not happen!"))
    useDirectly(eqMinusI, Seq(("t_", poly.term), ("s_", horner)), Seq(zeroPrv))
  }

  /**
    * invariant
    *   prv: \exists err. elem = poly + err & err \in [lower; upper]
    * */
  case class TM(elem: Term, poly: Polynomial, lower: Term, upper: Term, prv: ProvableSig) {
    assert(prv.conclusion.succ(0) == tmFormula(elem, poly, lower, upper))

    /** exact addition */
    def +!(other: TM) : TM = {
      val newPoly = poly.resetTerm + other.poly.resetTerm

      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveBinop(new BigDecimalTool)(prec)(IndexedSeq())(Plus)(lower, upper)(other.lower, other.upper)
      val newPrv = useDirectlyConst(weakenWithContext(plusPrv.fact), Seq(
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
      ), Seq(prv, other.prv, weakenWithContext(newPoly.representation), weakenWithContext(newIvlPrv)))
      TM(Plus(elem, other.elem), (poly + other.poly).resetTerm, l, u, newPrv)
    }

    /** approximate addition */
    def +(other: TM) : TM = (this +! (other)).approx(prec)

    /** exact subtraction */
    def -!(other: TM) : TM = {
      val newPoly = poly.resetTerm - other.poly.resetTerm

      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveBinop(new BigDecimalTool)(prec)(IndexedSeq())(Minus)(lower, upper)(other.lower, other.upper)
      val newPrv = useDirectlyConst(weakenWithContext(minusPrv.fact), Seq(
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
      ), Seq(prv, other.prv, weakenWithContext(newPoly.representation), weakenWithContext(newIvlPrv)))
      TM(Minus(elem, other.elem), (poly - other.poly).resetTerm, l, u, newPrv)
    }
    /** approximate subtraction */
    def -(other: TM) : TM = (this -! (other)).approx(prec)

    /** exact multiplication */
    def *!(other: TM) : TM = {
      val (polyLow, polyHigh, partitionPrv) = (poly.resetTerm * other.poly.resetTerm).partition{case (n, d, powers) => powers.sum <= order}

      val hornerPrv = toHorner(polyHigh)
      val rem = rhsOf(hornerPrv)
      val poly1 = rhsOf(poly.representation)
      val poly2 = rhsOf(other.poly.representation)
      def intervalBounds(i1: Term, i2: Term) : Term = Seq(rem, Times(i1, poly2), Times(i2, poly1), Times(i1, i2)).reduceLeft(Plus)
      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveBinop(new BigDecimalTool)(prec)(context)(intervalBounds)(lower, upper)(other.lower, other.upper)
      val newPrv = useDirectlyConst(weakenWithContext(timesPrv.fact), Seq(
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
        weakenWithContext(partitionPrv),
        weakenWithContext(polyLow.representation),
        weakenWithContext(hornerPrv),
        newIvlPrv))
      TM(Times(elem, other.elem), polyLow.resetTerm, l, u, newPrv)
    }
    /** approximate multiplication */
    def *(other: TM) : TM = (this *! (other)).approx(prec)

    /** exact negation */
    def unary_- : TM = {
      val newPoly = -(poly.resetTerm)

      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(prec)(IndexedSeq())(Neg)(lower, upper)
      val newPrv = useDirectlyConst(weakenWithContext(negPrv.fact), Seq(
        ("elem1_", elem),
        ("poly1_", rhsOf(poly.representation)),
        ("l1_", lower),
        ("u1_", upper),
        ("poly_", rhsOf(newPoly.representation)),
        ("l_", l),
        ("u_", u)
      ), Seq(prv, weakenWithContext(newPoly.representation), weakenWithContext(newIvlPrv)))
      TM(Neg(elem), (-poly).resetTerm, l, u, newPrv)
    }

    /** exact square */
    def squareExact : TM = {
      val (polyLow, polyHigh, partitionPrv) = (poly.resetTerm^2).partition{case (n, d, powers) => powers.sum <= order}
      val hornerPrv = toHorner(polyHigh)
      val rem = rhsOf(hornerPrv)
      val poly1 = rhsOf(poly.representation)
      def intervalBounds(i1: Term) : Term = Seq(rem, Times(Times(Number(2), i1), poly1), Power(i1, Number(2))).reduceLeft(Plus)
      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(prec)(context)(intervalBounds)(lower, upper)
      val newPrv = useDirectlyConst(weakenWithContext(squarePrv.fact), Seq(
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
      ), Seq(prv, weakenWithContext(partitionPrv),
        weakenWithContext(polyLow.representation),
        weakenWithContext(hornerPrv),
        newIvlPrv))
      TM(Power(elem, Number(2)), (polyLow).resetTerm, l, u, newPrv)
    }
    /** approximate square */
    def square : TM = (this.squareExact).approx(prec)

    /** approximate exponentiation */
    def ^(n: Int) : TM = n match {
      case 1 =>
        val newPrv = useDirectlyConst(weakenWithContext(powerOne.fact), Seq(
          ("elem1_", elem),
          ("poly1_", rhsOf(poly.representation)),
          ("l1_", lower),
          ("u1_", upper)),
          Seq(prv))
        TM(Power(elem, Number(1)), poly.resetTerm, lower, upper, newPrv)
      case n if n>0 && n%2 == 0 =>
        val m = n / 2
        val mPrv = ProvableSig.proveArithmetic(BigDecimalQETool, Equal(Number(n), Times(Number(2), Number(m))))
        val p = (this.^(m)).square
        val newPrv =
          useDirectlyConst(weakenWithContext(powerEven.fact), Seq(
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
            Seq(prv, p.prv, weakenWithContext(mPrv)))
        TM(Power(elem, Number(n)), p.poly.resetTerm, p.lower, p.upper, newPrv)
      case n if n>0 =>
        val m = n / 2
        val mPrv = ProvableSig.proveArithmetic(BigDecimalQETool, Equal(Number(n), Plus(Times(Number(2), Number(m)), Number(1))))
        val p = (this^m).square * this
        val newPrv =
          useDirectlyConst(weakenWithContext(powerOdd.fact), Seq(
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
            Seq(prv, p.prv, weakenWithContext(mPrv)))
        TM(Power(elem, Number(n)), p.poly.resetTerm, p.lower, p.upper, newPrv)
      case _ => throw new IllegalArgumentException("Taylor model ^ n requires n > 0, not n = " + n)
    }

    def approx(prec: Int) : TM = {
      val (polyApproxPrv, poly1, poly2) = poly.approx(prec)
      val poly1rep = rhsOf(poly1.representation)
      val poly2repPrv = toHorner(poly2)
      val poly2rep = rhsOf(poly2repPrv)
      val (ivlPrv, l2, u2) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(prec)(context)(i1 => Plus(poly2rep, i1))(lower, upper)
      val newPrv = useDirectlyConst(weakenWithContext(approxPrv.fact),
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
        Seq(prv, weakenWithContext(polyApproxPrv), weakenWithContext(poly1.representation), weakenWithContext(poly2repPrv), ivlPrv)
      )
      TM(elem, poly1.resetTerm, l2, u2, newPrv)
    }

  }

  def TM(elem: Term, poly: Polynomial, lower: Term, upper: Term, be: BelleExpr): TM = {
    TM(elem, poly, lower, upper,
      proveBy(Sequent(context, IndexedSeq(tmFormula(elem, poly, lower, upper))), be & done))
  }

  def Exact(elem: Polynomial): TM = {
    val newPrv = useDirectlyConst(weakenWithContext(exactPrv.fact),
      Seq(("elem_", elem.term), ("poly_", rhsOf(elem.representation))),
      Seq(weakenWithContext(elem.representation))
    )
    TM(elem.term, elem, Number(0), Number(0), newPrv)
  }

}
