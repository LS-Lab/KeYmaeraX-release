/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, SaturateTactic, TacticInapplicableFailure}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.TaylorModelTactics.{TaylorModel, debugTac}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ext.{BigDecimalTool, RingsLibrary}
import edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._

import scala.collection.immutable._

trait TaylorModelOptions {
  val precision: Integer
  val order: Integer
}

trait TimeStepOptions {
  def remainderEstimation(i: Integer) : (BigDecimal, BigDecimal)
}

/**
  * Taylor model arithmetic
  *
  * Here, a Taylor model is a data structure maintaining a proof that some term is element of the Taylor model.
  *
  * */
object TaylorModelArith {
  import PolynomialArithV2._
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

  /** takes a formula encoding a Taylor model and returns (elem, poly, lower, upper) */
  def destTaylorModelFormula(fml: Formula): (Term, Term, Term, Term) = fml match {
    case Exists(vars, And(Equal(elem, Plus(poly, ivl)), And(LessEqual(l, ivl1), LessEqual(ivl2, u)))) if
    vars.length == 1 && vars(0) == ivl && ivl == ivl1 && ivl == ivl2
    =>
      (elem, poly, l, u)
    case _ => throw new IllegalArgumentException("Taylor model formula of unexpected shape: " + fml)
  }

  private def weakenWith(context: IndexedSeq[Formula], prv: ProvableSig) : ProvableSig = {
    assert(prv.conclusion.ante.isEmpty)
    ProvableSig.startPlainProof(Sequent(context, prv.conclusion.succ)).apply(CoHideRight(SuccPos(0)), 0).apply(prv, 0)
  }

  /** @note: these are only here because .provable is horribly slow */
  val taylorModelPlusPrv = Ax.taylorModelPlusPrv.provable
  val taylorModelMinusPrv = Ax.taylorModelMinusPrv.provable
  val taylorModelCollectPrv = Ax.taylorModelCollectPrv.provable
  val taylorModelIntervalPrv = Ax.taylorModelIntervalPrv.provable
  val taylorModelPartitionPrv1 = Ax.taylorModelPartitionPrv1.provable
  val taylorModelEmptyIntervalPrv = Ax.taylorModelEmptyIntervalPrv.provable
  val taylorModelPartitionPrv2 = Ax.taylorModelPartitionPrv2.provable
  val taylorModelTimesPrv = Ax.taylorModelTimesPrv.provable
  val taylorModelDivideExactPrv = Ax.taylorModelDivideExactPrv.provable
  val taylorModelNegPrv = Ax.taylorModelNegPrv.provable
  val taylorModelSquarePrv = Ax.taylorModelSquarePrv.provable
  val taylorModelPowerOne = Ax.taylorModelPowerOne.provable
  val taylorModelPowerEven = Ax.taylorModelPowerEven.provable
  val taylorModelPowerOdd = Ax.taylorModelPowerOdd.provable
  val taylorModelApproxPrv = Ax.taylorModelApproxPrv.provable
  val taylorModelEvalPrv = Ax.taylorModelEvalPrv.provable
  val taylorModelTransElem = Ax.taylorModelTransElem.provable
  val taylorModelExactPrv = Ax.taylorModelExactPrv.provable


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
      val newPrv = useDirectlyConst(weakenWith(context, taylorModelPlusPrv), Seq(
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
      val newPrv = useDirectlyConst(weakenWith(context, taylorModelMinusPrv), Seq(
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

    private def hornerForm(poly: Polynomial) : ProvableSig = {
      // poly.hornerForm() // @note this fails too often because denominators get out of range
      poly.representation // fallback
    }

    /** collect terms of higher order in interval remainder */
    def collectHigherOrderTerms(implicit options: TaylorModelOptions) : TM = {
      val (polyLow, polyHigh, partitionPrv) = poly.resetTerm.partition{case (n, d, powers) => powers.degree <= options.order}
      val hornerPrv = hornerForm(polyHigh)
      val rem = rhsOf(hornerPrv)
      val poly1 = rhsOf(poly.representation)
      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(options.precision)(context)(i => Plus(rem, i))(lower, upper)
      val newPrv = useDirectlyConst(weakenWith(context, taylorModelCollectPrv), Seq(
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
    def interval(implicit options: TaylorModelOptions) : (Term, Term, ProvableSig) = {
      val hornerPrv = if(poly.variables.isEmpty) poly.resetTerm.representation else hornerForm(poly.resetTerm)
      val rem = rhsOf(hornerPrv)
      val poly1 = rhsOf(poly.representation)
      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(options.precision)(context)(i => Plus(rem, i))(lower, upper)
      (l, u,
        useDirectlyConst(weakenWith(context, taylorModelIntervalPrv), Seq(
        ("elem1_", elem),
        ("poly1_", poly1),
        ("l1_", lower),
        ("u1_", upper),

        ("rem_", rem),
        ("l_", l),
        ("u_", u)
      ), Seq(prv,
        weakenWith(context, hornerPrv),
        newIvlPrv)))
    }

    /** introduce new Taylor model (newElem) to partition this, formula required for weakening:
      * @return
      *   (elem = newElem + poly.filter(P) + [0, 0],
      *    newElem = poly.filter(!P) + [lower, upper],
      *    "newElem = ..."
      *    )
      * */
    def partition(newElem: Term, P: (BigDecimal, BigDecimal, PowerProduct) => Boolean)(implicit options: TaylorModelOptions) : (TM, TM, Equal) = {
      val (polyTrue, polyFalse, partitionPrv) = poly.resetTerm.partition(P)
      val poly1 = ofTerm(newElem) + polyTrue
      val poly2 = polyFalse
      val newElemEq = Equal(newElem, Minus(elem, polyTrue.term))
      val newContext = context:+newElemEq
      val newElemPrv = ProvableSig.startPlainProof(Sequent(newContext, IndexedSeq(newElemEq)))(Close(AntePos(context.length), SuccPos(0)), 0)
      val inst = Seq(
        ("elem_", elem),
        ("poly_", rhsOf(poly.representation)),
        ("l_", lower),
        ("u_", upper),

        ("polyTrue_", polyTrue.term),
        ("polyFalse_", polyFalse.term),

        ("newElem_", newElem),
        ("poly1_", rhsOf(poly1.representation)),
        ("poly2_", rhsOf(poly2.representation))
      )
      val assms = Seq(this.weakenContext(newElemEq).prv,
        weakenWith(newContext, partitionPrv),
        newElemPrv,
        weakenWith(newContext, poly1.representation),
        weakenWith(newContext, poly2.representation))
      val newPrv1 = useDirectlyConst(weakenWith(newContext, taylorModelPartitionPrv1), inst, assms)
      val newPrv2 = useDirectlyConst(weakenWith(newContext, taylorModelPartitionPrv2), inst, assms)
      (TM(elem, poly1.resetTerm, Number(0), Number(0), newPrv1),
        TM(newElem, poly2.resetTerm, lower, upper, newPrv2),
        newElemEq)
    }

    /** returns an equality, no quantifiers */
    def dropEmptyInterval: Option[ProvableSig] = if (lower == Number(0) && upper == Number(0)) Some {
      val poly1 = rhsOf(poly.representation)
      useDirectlyConst(weakenWith(context, taylorModelEmptyIntervalPrv), Seq(
        ("elem1_", elem),
        ("poly1_", poly1)
      ), Seq(prv))
    } else None

    /** exact multiplication */
    def *!(other: TM)(implicit options: TaylorModelOptions) : TM = {
      checkCompatibleContext(other)
      val (polyLow, polyHigh, partitionPrv) = (poly.resetTerm * other.poly.resetTerm).partition{case (n, d, powers) => powers.degree <= options.order}

      val hornerPrv = hornerForm(polyHigh)
      val rem = rhsOf(hornerPrv)
      val poly1 = rhsOf(poly.representation)
      val poly2 = rhsOf(other.poly.representation)
      def intervalBounds(i1: Term, i2: Term) : Term = Seq(rem, Times(i1, poly2), Times(i2, poly1), Times(i1, i2)).reduceLeft(Plus)
      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveBinop(new BigDecimalTool)(options.precision)(context)(intervalBounds)(lower, upper)(other.lower, other.upper)
      val newPrv = useDirectlyConst(weakenWith(context, taylorModelTimesPrv), Seq(
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

    /** exact division by constant */
    def /!(const: BigDecimal)(implicit options: TaylorModelOptions) : TM = {
      val inv = Divide(Number(1), Number(const))
      val q = Number(const)
      val r = Times(elem, inv)
      val numberPrv = useDirectly(divideNumber, Seq(
        ("p_", elem),
        ("q_", q),
        ("i_", q),
        ("r_", r)
        ), Seq(equalReflex(q), equalReflex(r)))
      val other = Exact(ofTerm(inv), context)
      val res = this *! other
      val newPrv = useDirectlyConst(weakenWith(context, taylorModelDivideExactPrv), Seq(
        ("elem1_", elem),
        ("inv_", inv),
        ("poly_", rhsOf(res.poly.representation)),
        ("l_", res.lower),
        ("u_", res.upper),
        ("elem2_", q)
      ), Seq(res.prv,
        weakenWith(context, numberPrv)))
      TM(Divide(elem, q), res.poly.resetTerm, res.lower, res.upper, newPrv)
    }
    /** approximate division */
    def /(const: BigDecimal)(implicit options: TaylorModelOptions) : TM = (this /! const).approx

    /** exact negation */
    def unary_-(implicit options: TaylorModelOptions) : TM = {
      val newPoly = -(poly.resetTerm)

      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(options.precision)(IndexedSeq())(Neg)(lower, upper)
      val newPrv = useDirectlyConst(weakenWith(context, taylorModelNegPrv), Seq(
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
      val (polyLow, polyHigh, partitionPrv) = (poly.resetTerm^2).partition{case (n, d, powers) => powers.degree <= options.order}
      val hornerPrv = hornerForm(polyHigh)
      val rem = rhsOf(hornerPrv)
      val poly1 = rhsOf(poly.representation)
      def intervalBounds(i1: Term) : Term = Seq(rem, Times(Times(Number(2), i1), poly1), Power(i1, Number(2))).reduceLeft(Plus)
      val (newIvlPrv, l, u) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(options.precision)(context)(intervalBounds)(lower, upper)
      val newPrv = useDirectlyConst(weakenWith(context, taylorModelSquarePrv), Seq(
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
        val newPrv = useDirectlyConst(weakenWith(context, taylorModelPowerOne), Seq(
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
          useDirectlyConst(weakenWith(context, taylorModelPowerEven), Seq(
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
          useDirectlyConst(weakenWith(context, taylorModelPowerOdd), Seq(
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
      val (polyApproxPrv, poly1, poly2) = poly.resetTerm.approx(options.precision)
      val poly1rep = rhsOf(poly1.representation)
      val poly2repPrv = hornerForm(poly2)
      val poly2rep = rhsOf(poly2repPrv)
      val (ivlPrv, l2, u2) = IntervalArithmeticV2.proveUnop(new BigDecimalTool)(options.precision)(context)(i1 => Plus(poly2rep, i1))(lower, upper)
      val newPrv = useDirectlyConst(weakenWith(context, taylorModelApproxPrv),
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
      val prettyRepresentation = poly.resetTerm.prettyRepresentation
      proveBy(ProvableSig.startPlainProof(Sequent(context, IndexedSeq(tmFormula(elem, rhsOf(prettyRepresentation),
        prettyLower, prettyUpper)))).apply(CutRight(prv.conclusion.succ(0), SuccPos(0)), 0).
        apply(CoHideRight(SuccPos(0)), 1).
        apply(ImplyRight(SuccPos(0)), 1),
        Idioms.<(
          by(prv),
          existsL(-1) & existsR("err_".asTerm)(1) & andL(-1) & andL(-2) & andR(1) &
          Idioms.<(
            cohideOnlyL(-1) &
              useAt(prettyRepresentation, PosInExpr(1::Nil))(1, 1::0::Nil) & id
            ,
            hideL(-1) & IntervalArithmeticV2.intervalArithmeticBool(options.precision, new BigDecimalTool)(1)
          )
        )
      )
    }

    /** insert arguments (arguments(i).elem must be a variable of this Taylor model) into this Taylor model */
    def evaluate(arguments: Seq[TM])(implicit options: TaylorModelOptions) : TM = {
      val vars = poly.variables
      val argumentMap = arguments.map(tm => (tm.elem, tm)).toMap
      val horner = hornerForm(poly.resetTerm)

      val evalPoly : TM = evalTerm(rhsOf(horner), context, argumentMap)
      val (ivlPrv, l, u) = IntervalArithmeticV2.proveBinop(new BigDecimalTool)(options.precision)(IndexedSeq())(Plus)(lower, upper)(evalPoly.lower, evalPoly.upper)
      val newPrv = useDirectlyConst(weakenWith(context, taylorModelEvalPrv),
        Seq(
          ("elem_", elem),
          ("poly1_", rhsOf(poly.representation)),
          ("l1_", lower),
          ("u1_", upper),
          ("polyrep_", rhsOf(horner)),
          ("poly2_", rhsOf(evalPoly.poly.representation)),
          ("l2_", evalPoly.lower),
          ("u2_", evalPoly.upper),
          ("l_", l),
          ("u_", u)
        ),
        Seq(prv, weakenWith(context, horner), evalPoly.prv, weakenWith(context, ivlPrv))
      )
      TM(elem, evalPoly.poly, l, u, newPrv)
    }

    def weakenContext(formula: Formula) = {
      val l = prv.conclusion.ante.length
      val newPrv = ProvableSig.startPlainProof(Sequent(prv.conclusion.ante++Seq(formula), prv.conclusion.succ)).
        apply(HideLeft(AntePos(l)), 0).
        apply(prv, 0)
      TM(elem, poly, lower, upper, newPrv)
    }

    def transElem(eqPrv: ProvableSig): TM = {
      require(eqPrv.isProved && eqPrv.conclusion.ante == context, "transElem requires proved equality with compatible context")
      val elem1 = lhsOf(eqPrv)
      val newPrv = useDirectlyConst(weakenWith(context, taylorModelTransElem),
        Seq(
          ("elem_", elem),
          ("elem1_", elem1),
          ("poly_", rhsOf(poly.representation)),
          ("l_", lower),
          ("u_", upper)
        ),
        Seq(prv, eqPrv)
      )
      TM(elem1, poly, lower, upper, newPrv)
    }

  }

  /** evaluate a Term in Taylor model arithmetic
    *  @note: this must be somewhat compatible with [[PolynomialArithV2.ofTerm]] */
  def evalTerm(t: Term, context: IndexedSeq[Formula], argumentMap: Map[Term, TM])(implicit options: TaylorModelOptions): TM = {
    require(argumentMap.forall{case (_, tm) => tm.context == context}, "require compatible contexts for evalTerm")
    def doEval(t: Term) : TM = t match {
      case Plus(a, b) => doEval(a) + doEval(b)
      case Minus(a, b) => doEval(a) - doEval(b)
      case Times(a, b) => doEval(a) * doEval(b)
      case Neg(a) => -doEval(a)
      case Power(a, Number(i)) if i.isValidInt && i >= 0 => doEval(a) ^ i.toIntExact
      case Power(_, _) => throw new IllegalArgumentException("Taylor model in exponent is not supported")
      case Divide(a, Number(i)) => doEval(a) / i
      case Divide(_, _) => throw new IllegalArgumentException("Taylor model in denominator is not supported")
      case Number(n) => Exact(ofTerm(Number(n)), context)
      case term: Term => argumentMap.get(term).getOrElse(Exact(ofTerm(term), context))
    }
    doEval(t)
  }

  val taylorModelIntervalLe = anyArgify(Ax.taylorModelIntervalLe.provable)
  val taylorModelIntervalGe = anyArgify(Ax.taylorModelIntervalGe.provable)
  val taylorModelIntervalLt = anyArgify(Ax.taylorModelIntervalLt.provable)
  val taylorModelIntervalGt = anyArgify(Ax.taylorModelIntervalGt.provable)

  /** try to prove a formula using Taylor model arithmetic */
  def evalFormula(fml: Formula, context: IndexedSeq[Formula], argumentMap: Map[Term, TM])(implicit options: TaylorModelOptions): Option[ProvableSig] = {
    require(argumentMap.forall{case (_, tm) => tm.context == context}, "require compatible contexts for evalFormula")
    def doEval(fml: Formula) : Option[ProvableSig] = fml match {
      case cmp: ComparisonFormula =>
        val f = cmp.left
        val g = cmp.right
        val diff = Minus(f, g)
        val (l, u, fgIvlPrv) = evalTerm(diff, context, argumentMap).interval
        val (cond, lemma) = cmp match {
          case LessEqual(_, _) => (LessEqual(u, Number(0)), taylorModelIntervalLe)
          case Less(_, _) => (Less(u, Number(0)), taylorModelIntervalLt)
          case GreaterEqual(_, _) => (GreaterEqual(l, Number(0)), taylorModelIntervalGe)
          case Greater(_, _) => (Greater(l, Number(0)), taylorModelIntervalGt)
        }
        try {
          val prv = ProvableSig.proveArithmetic(BigDecimalQETool, cond)
          prv.conclusion.succ(0) match {
            case Equiv(_, True) =>
              Some(useDirectly(weakenWith(context, lemma), Seq(("l_", l), ("u_", u), ("f_", f), ("g_", g)), Seq(fgIvlPrv, weakenWith(context, prv))))
            case _ => None
          }
        } catch {
          case _: IllegalArgumentException => None
        }
      case And(a, b) =>
        doEval(a) match {
          case Some(prva) =>
            doEval(b) match {
              case Some(prvb) =>
                Some(proveBy(Sequent(context, IndexedSeq(fml)), andR(1) & Idioms.<(by(prva), by(prvb))))
              case None => None
            }
          case None => None
        }
      case Or(a, b) =>
        doEval(a) match {
          case Some(prv) =>
            Some(proveBy(Sequent(context, IndexedSeq(fml)), orR(1) & hideR(2) & by(prv)))
          case None =>
            doEval(b) match {
              case Some(prv) =>
                Some(proveBy(Sequent(context, IndexedSeq(fml)), orR(1) & hideR(1) & by(prv)))
              case None => None
            }
        }
      case _ => throw new IllegalArgumentException("evalFormula does currently not support this formula: " + fml)
    }
    doEval(fml)
  }

  /** constructs a Taylor model by proving the required certificate with a tactic */
  def TM(elem: Term, poly: Polynomial, lower: Term, upper: Term, context: IndexedSeq[Formula], be: BelleExpr): TM = {
    TM(elem, poly, lower, upper,
      proveBy(Sequent(context, IndexedSeq(tmFormula(elem, rhsOf(poly.representation), lower, upper))), be & done))
  }

  /** constructs a Taylor model with zero interval part */
  def Exact(elem: Polynomial, context: IndexedSeq[Formula]): TM = {
    val newPrv = useDirectlyConst(weakenWith(context, taylorModelExactPrv),
      Seq(("elem_", elem.term), ("poly_", rhsOf(elem.representation))),
      Seq(weakenWith(context, elem.representation))
    )
    TM(elem.term, elem.resetTerm, Number(0), Number(0), newPrv)
  }

  // combines provables
  private def mkAndPrv(p1: ProvableSig, p2: ProvableSig) : ProvableSig = {
    assert(p1.conclusion.succ.length==1, "mkAndPrv singleton succedent 1")
    assert(p2.conclusion.succ.length==1, "mkAndPrv singleton succedent 2")
    assert(p1.conclusion.ante == p2.conclusion.ante, "mkAndPrv same antes")
    proveBy(Sequent(p1.conclusion.ante, IndexedSeq(And(p1.conclusion.succ(0), p2.conclusion.succ(0)))),
      andR(1) & Idioms.<(by(p1), by(p2))
    )
  }

  // combines provables
  private def equalTrans(p1: ProvableSig, p2: ProvableSig) : ProvableSig = {
    assert(p1.conclusion.succ.length==1, "mkAndPrv singleton succedent 1")
    assert(p2.conclusion.succ.length==1, "mkAndPrv singleton succedent 2")
    assert(p1.conclusion.ante == p2.conclusion.ante, "mkAndPrv same antes")
    val Llast = -p1.conclusion.ante.length - 1
    proveBy(Sequent(p1.conclusion.ante, IndexedSeq(Equal(lhsOf(p1), rhsOf(p2)))),
        cutR(p1.conclusion.succ(0))(1) &
        Idioms.<(
          by(p1),
            implyR(1) &
            eqL2R(Llast)(1) &
            hideL(Llast) &
            by(p2)
        )
    )
  }

  /** t subterm of s ? */
  def subtermOf(t: Term, s: Term) : Boolean =
    if (s == t)
      true
    else
      s match {
        case binop: BinaryCompositeTerm => subtermOf(t, binop.left) || subtermOf(t, binop.right)
        case unop: UnaryCompositeTerm => subtermOf(t, unop.child)
        case app: FuncOf => subtermOf(t, app.child)
        case a: AtomicTerm => false
        case _ => ???
      }
  /** t subterm of fml ? */
  def subtermOf(t: Term, fml: Formula) : Boolean = fml match {
    case cmp: ComparisonFormula => subtermOf(t, cmp.left) || subtermOf(t, cmp.right)
    case binop: BinaryCompositeFormula => subtermOf(t, binop.left) || subtermOf(t, binop.right)
    case unop: UnaryCompositeFormula => subtermOf(t, unop.child)
    case app: PredOf => subtermOf(t, app.child)
    case app: PredicationalOf => subtermOf(t, app.child)
    case m: Modal => throw new IllegalArgumentException("not expecting modal formula here")
    case q: Quantified => subtermOf(t, q.child)
    case a: AtomicFormula => false
    case _ => ???
  }

  val refineTmExists = Ax.refineTmExists.provable
  val refineConjunction = Ax.refineConjunction.provable
  val refineLe1 = Ax.refineLe1.provable
  val refineLe2 = Ax.refineLe2.provable

  def refineTaylorModelFormula(fml: Formula, assms: IndexedSeq[Formula])(implicit options: TaylorModelOptions) = {
    val case2 = assms.length == 2
    require(case2 || assms.length == 0, "only implemented for two cases")
    val (e, p, l, u) = destTaylorModelFormula(fml)
    val poly = PolynomialArithV2.ofTerm(p)
    val polyPrettyPrv = poly.prettyRepresentation
    val bounds = IntervalArithmeticV2.proveBounds(options.precision)(new BigDecimalTool)(assms)(true)(
      IntervalArithmeticV2.BoundMap(),
      IntervalArithmeticV2.BoundMap(),
      Map())(Seq(l, u))
    val lPrv = bounds._1(l)
    val l2 = lPrv.conclusion.succ(0).asInstanceOf[LessEqual].left
    val uPrv = bounds._2(u)
    val u2 = uPrv.conclusion.succ(0).asInstanceOf[LessEqual].right
    val tmFml = tmFormula(e, rhsOf(polyPrettyPrv), l2, u2)
    val imply = Imply(fml, tmFml)

    // @todo: performance critical?
    val implyPrv = proveBy(if (case2) Imply(assms.reduce(And), imply) else imply,
      (if (case2)(implyR(1) & andL(-1)) else skip) &
        useAt(refineTmExists, PosInExpr(1::Nil))(1) &
        allR(1) &
        useAt(refineConjunction, PosInExpr(1::Nil))(1) & andR(1) & Idioms.<(
        useAt(polyPrettyPrv, PosInExpr(0::Nil))(1, 0:: 1 :: 0 :: Nil) & implyR(1) & id,
        useAt(refineConjunction, PosInExpr(1 :: Nil))(1) & andR(1) & Idioms.<(
          useAt(refineLe2, PosInExpr(1 :: Nil))(1) & by(lPrv),
          useAt(refineLe1, PosInExpr(1 :: Nil))(1) & by(uPrv)
        )
      )
    )
    val tmRepFml = tmFormula(e, rhsOf(poly.representation), l2, u2)
    val iffPrv = proveBy(Equiv(tmFml, tmRepFml),
      useAt(polyPrettyPrv, PosInExpr(1::Nil))(1, 0::0::0::1::0::Nil) &
        useAt(poly.representation, PosInExpr(0::Nil))(1, 0::0::0::1::0::Nil) &
        byUS(Ax.equivReflexive)
    )
    (tmFml, tmRepFml, implyPrv, (e, poly.resetTerm, l2, u2, iffPrv))
  }

  /** delete formulas that contain ts from context, written "context \ ts" */
  def trimContext(context: Seq[Formula], ts: Seq[Term]) : Seq[Formula] =
    context.filter(fml => !ts.exists(subtermOf(_, fml)))

  /**
    * generic lemmas for evolution of ODE [[ode]] with Taylor model approiximations of order [[order]]
    * */
  class TemplateLemmas(ode: DifferentialProgram, order: Int) extends TaylorModel(ode, order) {

    /** Infrastructure for a concrete Taylor model time step:
      *
      * Input: (linearly) preconditioned Taylor model (TM_l o RM_r), initial time t0,
      * x0.provable: context |- x = TM_l(r) (zero interval term)
      * r0.provable: context |- r = TM_r(e)
      * t0:          context |- t = t0
      * (implicitly) context |- e \in [-1, 1] (suitable for IntervalArithmeticV2) // @todo: make these assumptions more explicit
      *
      * */
    class TimeStep(x0: Seq[TM], r0: Seq[TM], t0: ProvableSig, h: BigDecimal)(implicit options: TaylorModelOptions, timeStepOptions: TimeStepOptions) {
      val qeTool = new BigDecimalTool
      // x0 is the initial state of the ODE
      require(x0.map(_.elem) == state, "require x0 to be the initial state of the ODE")
      // x0 is the *linear* preconditioning, without interval uncertainty
      require(x0.forall(_.poly.degree() <= 1), "require x0 to be linear")
      require(x0.forall(_.lower == Number(0)), "require zero interval uncertainty(lower)")
      require(x0.forall(_.upper == Number(0)), "require zero interval uncertainty(upper)")

      val context = x0(0).context
      require(x0.forall(_.context == context), "require compatible contexts")

      require(lhsOf(t0) == time)

      val rvars = r0.map(_.elem).toIndexedSeq
      val rIntervals = r0.map(_.interval).toIndexedSeq

      def mkTerm(coeff: (BigDecimal, BigDecimal)): Term = Divide(Number(coeff._1), Number(coeff._2))

      val instantiation: USubstOne = instantiateLemma(options.precision,
        rhsOf(t0),
        Number(h),
        (i, j) => mkTerm(x0(i).poly.coefficient(ofSparse((rvars(j), 1)))),
        i => mkTerm(x0(i).poly.coefficient(ofSparse())),
        i => rIntervals(i)._1,
        i => rIntervals(i)._2,
        timeStepOptions.remainderEstimation
      ) ++ USubst(rvars.zipWithIndex.map { case (r, i) => SubstitutionPair(names.right(i), r) })

      // the suffix 1 somehow stands for instantiation
      val initialCondition1 = instantiation(initial_condition)
      val initialConditionFmls1 = FormulaTools.conjuncts(initialCondition1)
      val boxTMEnclosure1 = instantiation(boxTMEnclosure)
      val numbericCondition1 = instantiation(numbericCondition)

      val initialStateEqs = (x0, initialConditionFmls1.tail).zipped.map { case (x, Equal(y, t)) if x.elem == y =>
        val eq1 = x.dropEmptyInterval.getOrElse(throw new RuntimeException("intervals have been checked for emptiness"))
        val eq2 = weakenWith(x.context, x.poly.resetTerm.equate(ofTerm(t)).getOrElse(throw new RuntimeException("this equality should hold by construction: " +
          x.poly.resetTerm.term + " = " + ofTerm(t).term)))
        equalTrans(eq1, eq2)
      case e => throw new RuntimeException("Taylor model lemma (initial condition) not of expected shape: " + e)
      }
      val initialConditionPrv = (Seq(t0) ++ initialStateEqs).reduceRight(mkAndPrv)
      val rightTmDomainPrv = rIntervals.map(rIvl => rIvl._3).reduceRight(mkAndPrv)
      val numbericConditionPrv = proveBy(Sequent(context, IndexedSeq(numbericCondition1)),
        andR(1) & Idioms.<(
          debugTac("Initial Numberic condition") &
            SaturateTactic(andL('L)) &
            IntervalArithmeticV2.intervalArithmeticBool(options.precision, qeTool)(1) &
            done,
          SaturateTactic(allR(1)) &
            SaturateTactic(implyR(1)) &
            SaturateTactic(andL('L)) &
            debugTac("Numberic condition") &
            IntervalArithmeticV2.intervalArithmeticBool(options.precision, qeTool)(1) &
            done
        ))
      val numericAssumptionPrv = mkAndPrv(mkAndPrv(initialConditionPrv, rightTmDomainPrv), numbericConditionPrv)

      /*** computes a concrete Taylor Model in the variables r of the right Taylor model
        * [{x'=ode(x)&t0<=t&t<=t0+h}]x=TM(r)
        */
      def timeStepLemma : ProvableSig = proveBy(Sequent(context, IndexedSeq(boxTMEnclosure1)),
        useAt(lemma(instantiation), PosInExpr(1 :: Nil))(1) & by(numericAssumptionPrv)
      )

      require(0 <= h, "nonnegative time step")
      val nonnegativeTimeStep = {
        val fml = LessEqual(Number(0), Number(h))
        weakenWith(context, proveBy(fml,
          useAt(ProvableSig.proveArithmetic(BigDecimalQETool, fml), PosInExpr(0::Nil))(1) & closeT))
      }

      val (timeFml, taylorModelsFml) = boxTMEnclosure1 match {
        case Box(program, Exists(s, And(timeFml, taylorModelsFml))) if s.length == 1 => (timeFml, taylorModelsFml)
        case _ => throw new RuntimeException("timeStepLemma of unexpected shape")
      }
      val (timeEq, localTime, timebounds) = timeFml match {
        case And(telt@Equal(a, Plus(b, lt)), And(l@LessEqual(Number(c), d), u@LessEqual(e, Number(f))))
          if a == time && b == rhsOf(t0) && c.compareTo(0) == 0 && d == lt && e == lt && f.compareTo(h) == 0 =>
          (telt, lt, IndexedSeq(l, u))
        case _ => throw new RuntimeException("timeFml of unexpected shape: " + timeFml)
      }

      val t1Prv = ofTerm(Plus(rhsOf(t0), Number(h))).prettyRepresentation
      val t1 = rhsOf(t1Prv)
      val t1Eq = Equal(time, t1)

      val taylorModelsIvl = FormulaTools.conjuncts(taylorModelsFml).map(refineTaylorModelFormula(_, timebounds))

      /**
        * Computes concrete Taylor models to perform a time step on an (unbounded time) ode evolution:
        * @return (provable, TM_ivl, (TM_h, t1_eq))
        * where provable:
        *
        *             ivlContext          |-                                          eqContext      |-
        *                 "                                                              "
        * Γ, s ∈ [0, h], x = TM_ivl(s, r) |- P()              ;;              Γ, t=t0+h, x = TM_h(r) |- [{x'=ode(x)}]P
        * --------------------------------------------------------------------------------------------------------------
        *                                   Γ, t=t0, x=TM0(r) |- [{x'=ode(x)}]P
        *
        * TM_ivl.context = ivlContext
        * TM_h.context = eqContext
        * t1_eq: eqContext |- t=t0+h
        *
        */
      def timeStepLemma(P: Formula) : (ProvableSig, Seq[TM], Seq[TM], (Seq[TM], Seq[TM], ProvableSig)) = {
        val timeStepLemma1 = timestepLemma(instantiation)
        val taylorModelsFml1 = SubstitutionHelper.replaceFree(taylorModelsFml)(localTime, Number(h))
        val taylorModelsEq = FormulaTools.conjuncts(taylorModelsFml1).map (refineTaylorModelFormula(_, IndexedSeq()))
        val hideOldInitialState =
          context.zipWithIndex.flatMap{ case(fml, i) => if(vars.exists(subtermOf(_, fml))) Some(hideL(-i-1)) else None }.
            reverse.reduceLeftOption[BelleExpr](_ & _).getOrElse(skip)
        val saveRightTaylorModels = cut(r0.map(_.prv.conclusion.succ(0)).reduceRight(And)) & Idioms.<(skip, hideR(1) & by(r0.map(_.prv).reduceRight(mkAndPrv)))
        val prv = proveBy(Sequent(context, IndexedSeq(Box(ODESystem(ode, True), P))),
          useAt(timeStepLemma1, PosInExpr(1::Nil))(1) &
            andR(1) & Idioms.<(
            andR(1) & Idioms.<(
              andR(1) & Idioms.<(
                by(numericAssumptionPrv),
                by(nonnegativeTimeStep)
              ),
              cut(t0.conclusion.succ(0)) & Idioms.<(eqL2R(-context.length - 1)(1) & hideL('Llast), hideR(1) & by(t0)) &
                // "save" information about right Taylor models
                saveRightTaylorModels &
                // new initial state
                hideOldInitialState &
                allR(1) * vars.length &
                implyR(1) &
                andL('Llast) &
                cutL(taylorModelsIvl.map(_._1).reduceRight(And))('Llast) &
                Idioms.<(
                  SaturateTactic(andL('L)) & skip,
                  cohideOnlyR(2) &
                    taylorModelsIvl.init.foldRight[BelleExpr](
                      useAt(taylorModelsIvl.last._3, PosInExpr(1::Nil))(1) & id){ case ((_, _, implyPrv, _), tac) =>
                      useAt(refineConjunction, PosInExpr(1::Nil))(1) & andR(1) & Idioms.<(
                        useAt(implyPrv, PosInExpr(1::Nil))(1) & id,
                        tac
                      )
                    } & done
                )
            ),
            saveRightTaylorModels &
            // property throughout the time interval
            hideOldInitialState &
              allR(1) * vars.length &
              implyR(1) &
              cutL((t1Eq+:taylorModelsEq.map(_._1)).reduceRight(And))('Llast) & Idioms.<(
                SaturateTactic(andL('L)) & skip,
                cohideR(2) &
                  useAt(refineConjunction, PosInExpr(1::Nil))(1) & andR(1) & Idioms.<(
                    implyR(1) & useAt(t1Prv, PosInExpr(1::Nil))(1, 1::Nil) & id,
                    taylorModelsEq.init.foldRight[BelleExpr](
                      by(taylorModelsEq.last._3)){ case ((_, _, implyPrv, _), tac) =>
                      useAt(refineConjunction, PosInExpr(1::Nil))(1) & andR(1) & Idioms.<(
                        by(implyPrv),
                        tac
                      )
                    }
                  )
              )
          )
        )
        val contextIvl = prv.subgoals(0).ante
        val contextEq = prv.subgoals(1).ante
        val tmIvls = taylorModelsIvl.map{case (tmFml, tmRepFml, _, (elem, poly, l, u, iffPrv)) =>
          TM(elem, poly, l, u, proveBy(Sequent(contextIvl, IndexedSeq(tmRepFml)), useAt(iffPrv, PosInExpr(1::Nil))(1) & id))}
        val rTmIvls = r0.map(tm => TM(tm.elem, tm.poly, tm.lower, tm.upper, contextIvl, id))
        val tmEqs = taylorModelsEq.map{case (tmFml, tmRepFml, _, (elem, poly, l, u, iffPrv)) =>
          TM(elem, poly, l, u, proveBy(Sequent(contextEq, IndexedSeq(tmRepFml)), useAt(iffPrv, PosInExpr(1::Nil))(1) & id))}
        val rTmEqs = r0.map(tm => TM(tm.elem, tm.poly, tm.lower, tm.upper, contextEq, id))
        val t1 = proveBy(Sequent(contextEq, IndexedSeq(t1Eq)), id)
        (prv, tmIvls, rTmIvls, (tmEqs, rTmEqs, t1))
      }

    }

    /**
      * @param (x0, r0, t0) like for [[TimeStep]]
      *        prv: Provable with one subgoal of the form
      *           x = x0 o r0, t=t0 |- [{x'=ode(x)}]P(x)
      * @return (x1, r1, t1) suitable input to iterate this function (identity preconditioned)
      *         t1: proof of "t = t0 + h"
      *         prv1: Provable with one subgoal of the form
      *           x = x1 o r1, t = t0 +h |- [{x'=ode(x)}]P(x)
      * */
    def timeStepAndPrecondition(x0: Seq[TM], r0: Seq[TM], t0: ProvableSig, h: BigDecimal, prv: ProvableSig)(implicit options: TaylorModelOptions, timeStepOptions: TimeStepOptions) :
      (Seq[TM], Seq[TM], ProvableSig, ProvableSig) = {
      require(prv.subgoals.length==1, "timeStepAndPrecondition requires one subgoal")
      val subgoal = prv.subgoals(0)
      require(subgoal.succ.length==1, "timeStepAndPrecondition requires one succedent")
      val timestep = new TimeStep(x0, r0, t0, h)
      val P = subgoal.succ(0) match {
        case Box(ODESystem(prog, True), p) if prog == ode => p
        case _ => throw new IllegalArgumentException("timeStepAndPrecondition must be applied on a suitable unconstrained ODE evolution")
      }
      val (prv2, tmIvls, rIvls, (tmEqs, rEqs, tEq)) = timestep.timeStepLemma(P)
      val prvIvl = prv2.sub(0)
      val prvEq = prv2.sub(1)

      // prepare next step with preconditioning
      val (x1, r1, prvEq1) = identityPrecondition(tmEqs, rEqs, prvEq)
      val tEq1 = proveBy(Sequent(prvEq1.subgoals(0).ante, IndexedSeq(tEq.conclusion.succ(0))), id)
      val prv3 = prv.apply(prv2, 0).apply(prvEq1, 1)

      // solve safety for the last step
      val tms = tmIvls.map(_.evaluate(rIvls))
      val prv4 = evalFormula(prvIvl.conclusion.succ(0), prvIvl.subgoals(0).ante, tms.map(t=>(t.elem, t)).toMap) match {
        case Some(safetyPrv) => prv3.apply(safetyPrv, 0)
        case None => throw new TacticInapplicableFailure("Could not prove safety for the past time step: " + prvIvl.subgoals(0))
      }
      (x1, r1, tEq1, prv4)
    }

    /** the iteration of [[timeStepAndPrecondition]] */
    def iterateTimeSteps(x0: Seq[TM], r0: Seq[TM], t0: ProvableSig, h: BigDecimal, prv: ProvableSig, n: Int)(implicit options: TaylorModelOptions, timeStepOptions: TimeStepOptions) :
      (Seq[TM], Seq[TM], ProvableSig, ProvableSig) =
    if (n == 0) (x0, r0, t0, prv: ProvableSig)
    else {
      val (x1, r1, t1, prv1) = iterateTimeSteps(x0, r0, t0, h, prv, n - 1)
      timeStepAndPrecondition(x1, r1, t1, h, prv1)
    }

  }

  /**
    * partition and weaken a sequence of Taylor models
    * */
  def partition(xs: Seq[TM], newElems: Seq[Term], P: (BigDecimal, BigDecimal, PowerProduct)=>Boolean)(implicit options: TaylorModelOptions) : (Seq[TM], Seq[TM], Seq[Equal]) = {
    def doPartition(xs: Seq[TM], rs: Seq[TM], newElemEqs: Seq[Equal], x0s: Seq[TM], newElems: Seq[Term]) : (Seq[TM], Seq[TM], Seq[Equal]) =
      if(x0s.length == 0) (xs.reverse, rs.reverse, newElemEqs.reverse)
      else {
        val (x, r, newElemEq) = x0s.head.partition(newElems.head, (n: BigDecimal, d: BigDecimal, pp: PowerProduct) => pp.degree == 0)
        def weakenSeq(seq: Seq[TM]): Seq[TM] = seq.map(_.weakenContext(newElemEq))
        val newXs = x+:weakenSeq(xs)
        val newRs = r+:weakenSeq(rs)
        val newX0s = weakenSeq(x0s.tail)
        doPartition(newXs, newRs, newElemEq+:newElemEqs, newX0s, newElems.tail)
      }
    doPartition(Seq(), Seq(), Seq(), xs, newElems)
  }

  def cutEq(prv: ProvableSig, eq: Formula) = eq match {
    case Equal(v: Variable, rhs) =>
      val exEq = proveBy(Exists(Seq(v), eq), existsR(rhs)(1) & byUS(equalReflexive))
      proveBy(prv.apply(Cut(exEq.conclusion.succ(0)), 0)(HideRight(SuccPos(0)), 1)(CoHideRight(SuccPos(0)), 1)(exEq, 1),
        existsL('Llast)
      )
    case _ => throw new IllegalArgumentException("cutEq not with equality: " + eq)
  }
  def cutSeq(prvs: Seq[ProvableSig], prv: ProvableSig) : ProvableSig = {
    val cutEvals = prvs.init.foldLeft(prv(Cut(prvs.map(_.conclusion.succ(0)).reduceRight(And)), 0)(HideRight(SuccPos(0)), 1)){case (prv, x) =>
      prv(AndRight(SuccPos(0)), 1)(x, 1)
    }(prvs.last, 1)
    val L = cutEvals.subgoals(0).ante.length
    (L - 1 until L + prvs.length - 2).foldLeft(cutEvals){ case (prv, i) => prv(AndLeft(AntePos(i)), 0) }
  }

  def hideAntes(hides: Seq[Int], prv: ProvableSig) = {
    hides.foldLeft(prv){case (p, i) => p(HideLeft(AntePos(i)), 0) }
  }

  /**
    * @param x = lTM(r) ... (left) Taylor model with variables in r
    *        r = rTM(e) ... (right) Taylor model with variables in e
    * @return (x1, r1) ...
    *         x1 = r + c ... identity part of (lTM o rTM)
    *         r1 = rTM'(e, i) ... higher order terms + a fresh variable for symbolic remainders
    *
    * x = r + c
    * r0 = TM(e, i)
    * */
  def identityPrecondition(x: Seq[TM], r: Seq[TM], prv: ProvableSig)(implicit options: TaylorModelOptions) : (Seq[TM], Seq[TM], ProvableSig) = {
    require(prv.subgoals.length==1, "identityPrecondition requires one subgoal")
    val subgoal = prv.subgoals(0)
    val context = x(0).context // @note could check for compatibility of all contexts?
    require(subgoal.ante == context)

    // Evaluate (x o r)
    val x1 = x.map(_.evaluate(r))
    val hidevars = x.map(_.elem) ++ r.map(_.elem)
    val hides = context.zipWithIndex.reverse.flatMap{ case (fml, i) =>
      if (hidevars.exists(subtermOf(_, fml))) Some(i)
      else None
    }
    val prv2 = cutSeq(x1.map(_.prv), prv)
    val onlyEvals = hideAntes(hides, prv2)

    // partition x = Id(r) & r = ...
    val context2 = onlyEvals.subgoals(0).ante
    val r1s = r.map(_.elem)
    val x1s = x1.map(tm => TM(tm.elem, tm.poly, tm.lower, tm.upper, context2, id))
    val (nxs, nrs, newEqs) = partition(x1s, r1s,  (n: BigDecimal, d: BigDecimal, pp: PowerProduct) => pp.degree == 0)

    val prv3 = newEqs.foldLeft(onlyEvals)(cutEq)
    val context3 = prv3.subgoals(0).ante

    val prv4 = cutSeq((nxs++nrs).map(_.prv), prv3)
    val context4 = prv4.subgoals(0).ante

    val x4s = x1.map(tm => TM(tm.elem, tm.poly, tm.lower, tm.upper, context4, id))
    val argumentMap = x4s.map(tm => (tm.elem, tm)).toMap
    val intervals = newEqs.map{fml =>
      val i = context4.indexOf(fml)
      val eqPrv = proveBy(Sequent(context4, IndexedSeq(fml)), cohideOnlyL(-i - 1) & id)
      (i, evalTerm(fml.right, context4, argumentMap).transElem(eqPrv).interval)
    }.sortBy{case (i, _) => -i}.toIndexedSeq
    val prv5 = hideAntes(intervals.map(_._1), cutSeq(intervals.map(_._2._3), prv4))
    val context5 = prv5.subgoals(0).ante
    val prv6 = (context5.length - x1.length until context5.length).reverse.foldLeft(prv5){case (prv, i) =>
      prv(AndLeft(AntePos(i)), 0)
    }
    val prv7 = hideAntes((context2.length - x1.length until context2.length).reverse, prv6)
    val context7 = prv7.subgoals(0).ante

    (nxs.map(tm => TM(tm.elem, tm.poly, tm.lower, tm.upper, context7, id)),
      nrs.map(tm => TM(tm.elem, tm.poly, tm.lower, tm.upper, context7, id)),
      prv7)
  }

}
