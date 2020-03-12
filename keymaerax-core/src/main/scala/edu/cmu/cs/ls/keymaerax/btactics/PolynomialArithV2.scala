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

import scala.collection.immutable._

/**
  * Polynomial Arithmetic
  *
  * Constructed for a given List of variables (e.g., Seq(x1, ..., xn)).
  * Computations are carried out fairly efficiently in a distributive representation.
  *
  * A polynomial is represented as a set of monomials stored in a 2-3 Tree, the ordering is lexicographic
  * A monomial is represented as a coefficient and a power-product.
  * A coefficient is represented as a pair of BigDecimals for num/denum.
  * A power product is represented densely as a list of exponents
  *
  * All data-structures maintain a proof of
  *  input term = normal form of representation
  *
  * the normal form of a 3-Node (l, v1, m, v2, r) is "l + v1 + m + v2 + r"
  * the normal form of a 2-Node (l, v, r) is "l + v + r"
  * the normal form of a monomial (c, pp) is "c * pp"
  * the normal form of a coefficient (num, denum) is "num / denum"
  * the normal form of a power product [e1, ..., en] is "x1^e1 * ... * xn ^ en",
  *   where instead of "x^0", we write "1" in order to avoid trouble with 0^0, i.e., nonzero-assumptions on x or the like
  *
  * All operations on the representations update the proofs accordingly.
  *
  * @author Fabian Immler.
  */

object PolynomialArithV2 {

  // TODO: move somewhere reasonable
  def constR(name: String) = FuncOf(Function(name, None, Unit, Real), Nothing)
  def anyR(name: String) = UnitFunctional(name, AnyArg, Real)

  private def substAny(s: String, t: Term) = USubst(Seq(SubstitutionPair(anyR(s), t)))

  def anyArgify(prv: ProvableSig) = {
    require(prv.isProved)
    val us = USubst(StaticSemantics.signature(prv.conclusion).flatMap{
      case f@Function(n, None, Unit, Real, false) => Some(SubstitutionPair(FuncOf(f, Nothing), UnitFunctional(n, AnyArg, Real)))
      case _ => None
    }.toIndexedSeq)
    prv(us)
  }

  val equalReflex = anyArgify(DerivedAxioms.equalReflex.fact)
  val spat = "s_(||)".asTerm
  def equalReflex(t: Term) : ProvableSig = equalReflex(USubst(Seq(SubstitutionPair(spat, t))))

  def substOfInst(inst: Seq[(String, Term)]) = USubst(inst.map{case(a, b) => SubstitutionPair(anyR(a), b)})
  def useDirectly(prv: ProvableSig, inst: Seq[(String, Term)], assms: Seq[ProvableSig]) : ProvableSig = {
    val prv2 = prv(substOfInst(inst))
    impliesElim(prv2, assms)
  }

  // TODO: use sequents here?!
  // P->Q   P
  // ---------
  // Q
  def impliesElim(PQ: ProvableSig, P: ProvableSig) : ProvableSig = {
    require(PQ.isProved)
    require(P.isProved)
    require(PQ.conclusion.ante.length == 0)
    require(PQ.conclusion.succ.length == 1)
    require(P.conclusion.ante.length == 0)
    require(P.conclusion.succ.length == 1)
    val pq = PQ.conclusion.succ(0)
    val p = P.conclusion.succ(0)
    pq match {
      case Imply(pp, q) => ProvableSig.startProof(q)(CutRight(p, SuccPos(0)), 0)(PQ, 1)(P, 0)
      case _ => throw new IllegalArgumentException("Cannot impliesElim here")
    }
  }

  def impliesElim(PsQ: ProvableSig, Ps: Seq[ProvableSig]) : ProvableSig =
  if (Ps.length == 0) PsQ
  else {
    val conj = Ps.map(P => P.conclusion.succ(0)).reduceRight(And)
    val conjPrv = Ps.dropRight(1).foldLeft(ProvableSig.startProof(conj)){(prv, P) =>
      prv(AndRight(SuccPos(0)), 0)(P, 0)
    }(Ps.last, 0)
    impliesElim(PsQ, conjPrv)
  }

  def rememberAny(fml: Formula, be: BelleExpr) = anyArgify(remember(fml, be).fact)

  def byExact(assm: ProvableSig) = "byExact" by { (prv: ProvableSig, pos: SuccPosition) =>
    assert(prv.subgoals.length==1, "require one subgoal byExact")
    prv.apply(assm, 0)
  }
}

case class PolynomialArithV2(vars: IndexedSeq[Term]) {
  import PolynomialArithV2._

  val constL = constR("l_")
  val constR_ = constR("r_")
  val constCl = constR("cl_")
  val constCr = constR("cr_")
  val constC = constR("c_")


  val constLn = constR("ln")
  val constLd = constR("ld")
  val constRn = constR("rn")
  val constRd = constR("rd")
  val coefficientTimesPrv = rememberAny(
    ("(l() = ln()/ld() & r() = rn()/rd() & ((ln()*rn() = pn() & ld()*rd()=pd() & ld() != 0 & rd() != 0)<-> true)) ->" +
      "l()*r() = pn()/pd()").asFormula, QE & done)

  val coefficientPlusPrv = rememberAny(
    ("(l() = ln()/ld() & r() = rn()/rd() & ((ln()*rd() + rn()*ld() = pn() & ld()*rd()=pd() & ld() != 0 & rd() != 0)<-> true)) ->" +
      "l()+r() = pn()/pd()").asFormula, QE & done)

  /**
  * prv: lhs = rhs
  * lhs: input term (arbitrary, trace of construction)
  * rhs: Divide(Number(num), Number(denum))
  */
  case class Coefficient(num: BigDecimal, denum: BigDecimal,
                         prvO: Option[ProvableSig] = None) {
    val numN = Number(num)
    val denumN = Number(denum)
    // @note detour for "dependent" default argument
    lazy val defaultPrv = equalReflex(Divide(numN, denumN))
    val prv = prvO.getOrElse(defaultPrv)
    def forgetPrv = Coefficient(num, denum, Some(defaultPrv))

    assert(prv.subgoals.isEmpty)
    assert(prv.conclusion.ante.isEmpty)
    assert(prv.conclusion.succ.length==1)
    assert(prv.conclusion.succ(0) match {
      case Equal(lhs, Divide(Number(n), Number(d))) => n == num && d == denum
      case _ => false
    })
    val (eq, lhs, rhs) = prv.conclusion.succ(0) match { case eq @ Equal(lhs, rhs@Divide(n, d)) => (eq, lhs, rhs) }

    def +(that: Coefficient) : Coefficient = {
      val numRes = num*that.denum + that.num*denum
      val denumRes = denum*that.denum
      val inst = Seq(
        ("ln", numN),
          ("ld", denumN),
          ("rn", that.numN),
          ("rd", that.denumN),
          ("l", lhs),
          ("r", that.lhs),
          ("pn", Number(numRes)),
          ("pd", Number(denumRes)))
      val numericPrv = ProvableSig.proveArithmetic(BigDecimalQETool,
        List(
          Equal(Plus(Times(numN, that.denumN), Times(that.numN, denumN)), Number(numRes)),
          Equal(Times(denumN, that.denumN), Number(denumRes)),
          NotEqual(denumN, Number(0)),
          NotEqual(that.denumN, Number(0)),
        ).reduceRight(And)
      )
      val prvRes = useDirectly(coefficientPlusPrv, inst, Seq(prv, that.prv, numericPrv))
      Coefficient(numRes, denumRes, Some(prvRes))
    }

    def *(that: Coefficient) : Coefficient = {
      val numRes = num*that.num
      val denumRes = denum*that.denum
      val inst = Seq(
        ("ln", numN),
          ("ld", denumN),
          ("rn", that.numN),
          ("rd", that.denumN),
          ("l", lhs),
          ("r", that.lhs),
          ("pn", Number(numRes)),
          ("pd", Number(denumRes)))
      val numericPrv = ProvableSig.proveArithmetic(BigDecimalQETool,
        List(
          Equal(Times(numN, that.numN), Number(numRes)),
          Equal(Times(denumN, that.denumN), Number(denumRes)),
          NotEqual(denumN, Number(0)),
          NotEqual(that.denumN, Number(0)),
        ).reduceRight(And)
      )
      val prvRes = useDirectly(coefficientTimesPrv, inst, Seq(prv, that.prv, numericPrv))
      Coefficient(numRes, denumRes, Some(prvRes))
    }
  }

  val identityTimes = rememberAny("1*f_() = f_()".asFormula, QE & done)
  val timesIdentity = rememberAny("f_()*1 = f_()".asFormula, QE & done)

  val plusTimes = rememberAny("l_() = a_()*b_() & r_() = c_()*b_() & a_() + c_() = d_() -> l_() + r_() = d_()*b_()".asFormula, QE & done)

  private val maxDegree = 20
  private def powerLemmaFormula(i: Int, j: Int) = {
    val x = constR("x_")
    Equal(Times(Power(x, Number(i)), Power(x, Number(j))), Power(x, Number(i + j)))
  }
  val powerLemmaCache =
    (for (i <- 1 to maxDegree; j <- 1 to maxDegree) yield
      ((i, j), rememberAny(powerLemmaFormula(i, j), QE & done))).toMap

  def powerLemma(i: Int, j: Int) = powerLemmaCache.get((i, j)).getOrElse(
    ??? // todo: could do this: rememberAny(powerLemma(i, j), QE & done), but keeping the error to catch potential performance issues when calling QE?
  )
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
  val monomialTimesLemma = {
    val l = constL
    val cl = constCl
    def xl(i: Int) = mkConst("xl", i)
    val xls = (0 until vars.length).map(xl)
    val r = constR_
    val cr = constCr
    def xr(i: Int) = mkConst("xr", i)
    val xrs = (0 until vars.length).map(xr)

    val c = mkConst("c", 0)
    def x(i: Int) = mkConst("x", i)
    val xs = (0 until vars.length).map(x)

    val powersAssm = (0 until vars.length).map(i => Equal(Times(xl(i), xr(i)), x(i))).reduceRight(And)
    val assms = Seq(
      Equal(l, Times(cl, xls.reduceLeft(Times))),
      Equal(r, Times(cr, xrs.reduceLeft(Times))),
      Equal(Times(cl, cr), c),
      powersAssm).reduceRight(And)
    val concl = Equal(Times(l, r), Times(c, xs.reduceLeft(Times)))
    rememberAny(Imply(assms, concl), QE & done)
  }

  def variablePower(powers: Int => Int)(i: Int) = {
    val p = powers(i)
    if (p > 0) Power(vars(i), Number(p)) else Number(1)
  }

  val constF = anyR("f_")
  val constX = anyR("x_")

  /**
    * prv: lhs = rfhs
    * lhs: input term (arbitrary, trace of construction)
    * rhs: normalized form of `coeff*vars^powers`
    * */
  case class Monomial(coeff: Coefficient, powers: IndexedSeq[Int], prvO: Option[ProvableSig] = None) extends Ordered[Monomial] {

    def monomialTerm(coeff: Term, powers: IndexedSeq[Int]) : Term = {
      Times(coeff, (0 until vars.length).map(variablePower(powers)).reduceLeft(Times))
    }

    def powersString: String =
      (0 until vars.length).map(i => if (powers(i)>0) (Power(vars(i), Number(powers(i)))).toString else "").mkString

    lazy val defaultPrv = equalReflex(monomialTerm(coeff.rhs, powers))
    def forgetPrv = Monomial(coeff, powers, Some(defaultPrv))
    // @note detour for "dependent" default argument
    val prv = prvO.getOrElse(defaultPrv)

    // @todo: finish proof!
    //assert(prv.subgoals.isEmpty)
    assert(prv.conclusion.ante.isEmpty)
    assert(prv.conclusion.succ.length==1)
    assert(prv.conclusion.succ(0) match {
      case Equal(_, rhs) => rhs == monomialTerm(coeff.rhs, powers)
      case _ => false
    })
    val (eq, lhs, rhs) = prv.conclusion.succ(0) match { case eq @ Equal(lhs, rhs@(Times(_, _))) => (eq, lhs, rhs) }

    private def solvePowers(prv: ProvableSig, i: Int) : ProvableSig = {
      prv.subgoals(i).succ(0) match {
        case And(_, _) =>
          solvePowers(solvePowers(prv(AndRight(SuccPos(0)), i), i+1), i)
        case Equal(Times(Number(_), f), _) =>
          // 1 * f = f
          prv(identityTimes(USubst(SubstitutionPair(constF, f)::Nil)), i)
        case Equal(Times(f, Number(_)), _) =>
          // f * 1 = f
          prv(timesIdentity(USubst(SubstitutionPair(constF, f)::Nil)), i)
        case Equal(Times(Power(x, Number(n)), Power(_, Number(m))), _) =>
          // _^i * _^j = _^(i+j)
          prv(powerLemma(n.toIntExact, m.toIntExact)(USubst(SubstitutionPair(constX, x)::Nil)), i)
        case e =>
          ???
      }
    }

    def *(that: Monomial) : Monomial = {
      val newCoeff = coeff.forgetPrv * that.coeff.forgetPrv
      val newPowers = (powers, that.powers).zipped.map(_ + _)
      // TODO: just use a match for simplicity?
      val inst = Seq(("l_", lhs),
          ("r_", that.lhs),
          ("cl_", coeff.rhs),
          ("cr_", that.coeff.rhs),
          ("c0_", newCoeff.rhs)
        ) ++
          (0 until vars.length).map(i => (mkConstN("xl", i), variablePower(powers)(i))) ++
          (0 until vars.length).map(i => (mkConstN("xr", i), variablePower(that.powers)(i))) ++
          (0 until vars.length).map(i => (mkConstN("x", i), variablePower(newPowers)(i)))
      val monomialTimesLemmaInst = monomialTimesLemma(substOfInst(inst))
      val powersFml = monomialTimesLemmaInst.conclusion.succ(0) match {
        case Imply(And(_, And(_, And(_, powersFml))), _) => powersFml
        case _ => throw new RuntimeException("powersAssm???")
      }
      val powersPrv = solvePowers(ProvableSig.startProof(powersFml), 0)
      val newPrv = impliesElim(monomialTimesLemmaInst, Seq(prv, that.prv, newCoeff.prv, powersPrv))
      Monomial(newCoeff, newPowers, Some(newPrv))
    }

    // TODO: weird signature for addition...
    def +(that: Monomial): Option[Monomial] = if (that.powers == powers) Some {
      val newCoeff = coeff.forgetPrv + that.coeff.forgetPrv

      val inst = Seq(("l_", lhs), ("r_", that.lhs), ("a_", coeff.rhs), ("b_", rhs.right), ("c_", that.coeff.rhs), ("d_", newCoeff.rhs))
      val newPrv = useDirectly(plusTimes, inst, Seq(prv, that.prv, newCoeff.prv))
      Monomial(newCoeff, powers, Some(newPrv))
    } else None

    // reverse lexicographic ordering, TODO: why not thats?
    override def compare(that: Monomial): Int = {
      val l = vars.length
      def compareAt(i: Int) : Int =
        if (i >= l) 0
        else {
          val c = powers(i).compare(that.powers(i))
          if (c == 0) compareAt(i + 1)
          else c
        }
      // note *reverse*
      -compareAt(0)
    }
  }

  val zez = rememberAny("0 = 0".asFormula, byUS(DerivedAxioms.equalReflex))

  val emptySprout = rememberAny("s_() = 0 & t_() = u_() -> s_() + t_() = 0 + u_() + 0".asFormula, QE & done)

  // Lemmas for insert (i.e., add monomial)

  // @todo: should these be constructed more systematically?! e.g., define common subformulas only once. would make the code more robust...
  val branch2Left  = rememberAny("t_() = l_() + v_() + r_() & l_() + x_() = lx_() -> t_() + x_() = lx_() + v_()  + r_() ".asFormula, QE & done)
  val branch2Value = rememberAny("t_() = l_() + v_() + r_() & v_() + x_() = vx_() -> t_() + x_() = l_()  + vx_() + r_() ".asFormula, QE & done)
  val branch2Right = rememberAny("t_() = l_() + v_() + r_() & r_() + x_() = rx_() -> t_() + x_() = l_()  + v_()  + rx_()".asFormula, QE & done)

  /** @note for the Left case, could actually just use [[branch2Left]] */
  val branch2GrowLeft =  rememberAny("t_() = l_() + v_() + r_() & l_() + x_() = l1_() + lv_() + l2_() -> t_() + x_() = l1_() + lv_() + l2_() + v_() + r_()                 ".asFormula, QE & done)
  val branch2GrowRight = rememberAny("t_() = l_() + v_() + r_() & r_() + x_() = r1_() + rv_() + r2_() -> t_() + x_() = l_()                  + v_() + r1_() + rv_() + r2_()".asFormula, QE & done)

  val branch3Left =   rememberAny("t_() = l_() + v_() + m_() + w_() + r_() & l_() + x_() = lx_() -> t_() + x_() = lx_() + v_()  + m_()  + w_()  + r_() ".asFormula, QE & done)
  val branch3Value1 = rememberAny("t_() = l_() + v_() + m_() + w_() + r_() & v_() + x_() = vx_() -> t_() + x_() = l_()  + vx_() + m_()  + w_()  + r_() ".asFormula, QE & done)
  val branch3Mid =    rememberAny("t_() = l_() + v_() + m_() + w_() + r_() & m_() + x_() = mx_() -> t_() + x_() = l_()  + v_()  + mx_() + w_()  + r_() ".asFormula, QE & done)
  val branch3Value2 = rememberAny("t_() = l_() + v_() + m_() + w_() + r_() & w_() + x_() = wx_() -> t_() + x_() = l_()  + v_()  + m_()  + wx_() + r_() ".asFormula, QE & done)
  val branch3Right =  rememberAny("t_() = l_() + v_() + m_() + w_() + r_() & r_() + x_() = rx_() -> t_() + x_() = l_()  + v_()  + m_()  + w_()  + rx_()".asFormula, QE & done)

  val branch3GrowLeft = rememberAny(("t_() = l_() + v_() + m_() + w_() + r_() & l_() + x_() = l1_() + lv_() + l2_() ->" +
    "t_() + x_() = (l1_() + lv_() + l2_()) + v_()  + (m_()  + w_()  + r_())").asFormula, QE & done)

  val branch3GrowMid = rememberAny(("t_() = l_() + v_() + m_() + w_() + r_() & m_() + x_() = m1_() + mv_() + m2_() ->" +
    "t_() + x_() = (l_() + v_() + m1_()) + mv_()  + (m2_()  + w_()  + r_())").asFormula, QE & done)
  val branch3GrowRight = rememberAny(("t_() = l_() + v_() + m_() + w_() + r_() & r_() + x_() = r1_() + rv_() + r2_() ->" +
    "t_() + x_() = (l_() + v_() + m_()) + w_()  + (r1_()  + rv_()  + r2_())").asFormula, QE & done)

  // Lemmas for Add
  val plusEmpty = rememberAny(("t_() = s_() & u_() = 0 -> t_() + u_() = s_()").asFormula, QE & done)
  val plusBranch2 = rememberAny(("(s_() = l_() + v_() + r_() & t_() + l_() + v_() + r_() = sum_()) ->" +
    "t_() + s_() = sum_()").asFormula, QE & done)
  val plusBranch3 = rememberAny(("(s_() = l_() + v1_() + m_() + v2_() + r_() & t_() + l_() + v1_() + m_() + v2_() + r_() = sum_()) ->" +
    "t_() + s_() = sum_()").asFormula, QE & done)

  // Lemmas for Times Monomial
  val monTimesZero = rememberAny("t_() = 0 -> t_() * x_() = 0".asFormula, QE & done)
  val monTimesBranch2 = rememberAny(
    ("(t_() = l_() + v_() + r_() &" +
      "l_() * x_() = lx_() &" +
      "v_() * x_() = vx_() &" +
      "r_() * x_() = rx_()) -> t_() * x_() = lx_() + vx_() + rx_()").asFormula, QE & done)
  val monTimesBranch3 = rememberAny(
    ("(t_() = l_() + v1_() + m_() + v2_() + r_() &" +
      "l_() * x_() = lx_() &" +
      "v1_() * x_() = v1x_() &" +
      "m_() * x_() = mx_() &" +
      "v2_() * x_() = v2x_() &" +
      "r_() * x_() = rx_()) -> t_() * x_() = lx_() + v1x_() + mx_() + v2x_() + rx_()").asFormula, QE & done)

  // Lemmas for Times
  val timesEmpty = rememberAny(("t_() = 0 -> t_() * u_() = 0").asFormula, QE & done)
  val timesBranch2 = rememberAny(("(t_() = l_() + v_() + r_() & l_()*u_() + u_() * v_() + r_()*u_() = sum_()) ->" +
    "t_() * u_() = sum_()").asFormula, QE & done)
  val timesBranch3 = rememberAny(("(t_() = l_() + v1_() + m_() + v2_() + r_() & l_()*u_() + u_()*v1_() + m_()*u_() + u_()*v2_() + r_()*u_() = sum_()) ->" +
    "t_() * u_() = sum_()").asFormula, QE & done)

  // Lemmas for Power
  lazy val powerZero = rememberAny(("1 = one_() -> t_() ^ 0 = one_()").asFormula, QE & done)
  lazy val powerOne = rememberAny(("t_() = s_() -> t_() ^ 1 = s_()").asFormula, QE & done)
  val powerEven = rememberAny(("((n_() = 2*m_() <-> true) & t_()^m_() = p_() & p_()*p_() = r_()) ->" +
    "t_() ^ n_() = r_()").asFormula,
    implyR(1) & andL(-1) & andL(-2) &
      useAt(DerivedAxioms.equivTrue, PosInExpr(0::Nil))(-1) &
      eqL2R(-1)(1) & hideL(-1) &
      cutR("t_() ^ (2*m_()) = (t_()^m_())^2".asFormula)(1) & Idioms.<(
      QE & done,
      implyR(1) & eqL2R(-3)(1) & hideL(-3) & eqL2R(-1)(1) & hideL(-1) & QE & done
    )
  )
  val powerOdd = rememberAny(("((n_() = 2*m_() + 1 <-> true) & t_()^m_() = p_() & p_()*p_()*t_() = r_()) ->" +
    "t_() ^ n_() = r_()").asFormula,
    implyR(1) & andL(-1) & andL(-2) &
      useAt(DerivedAxioms.equivTrue, PosInExpr(0::Nil))(-1) &
      eqL2R(-1)(1) & hideL(-1) &
      cutR("t_() ^ (2*m_() + 1) = (t_()^m_())^2*t_()".asFormula)(1) & Idioms.<(
      QE & done,
      implyR(1) & eqL2R(-3)(1) & hideL(-3) & eqL2R(-1)(1) & hideL(-1) & QE & done
    )
  )

  /**
    * 2-3 Tree for monomials, keeping track of proofs.
    * */
  sealed trait Growth
  case class Stay(p: Polynomial) extends Growth
  case class Sprout(sprout: Branch2) extends Growth
  // Inner node, i.e., one with content

  sealed trait Polynomial {
    val prv: ProvableSig
    def forgetPrv: Polynomial
    def treeSketch: String
    lazy val (eq, lhs, rhs) = prv.conclusion.succ(0) match { case eq @ Equal(lhs, rhs) => (eq, lhs, rhs) }

    def lookup(x: Monomial) : Option[Monomial] = this match {
      case Empty(_) => None
      case Branch2(left, v, right, _) => x.compare(v) match {
        case 0 => Some(v)
        case c if c < 0 => left.lookup(x)
        case c if c > 0 => right.lookup(x)
      }
      case Branch3(left, v1, mid, v2, right, _) => x.compare(v1) match {
        case 0 => Some(v1)
        case c if c < 0 => left.lookup(x)
        case c if c > 0 => x.compare(v2) match {
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
        x.compare(v) match {
        case 0 =>
          val vx = (v.forgetPrv+x).get
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
        x.compare(v) match {
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
            x.compare(w) match {
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
    def +(m: Monomial) : Polynomial = insert(m) match {
      case Stay(p) => p
      case Sprout(s) => s
    }

    private[PolynomialArithV2] def updatePrv(prv2: ProvableSig) : Polynomial = {
      this match {
        case Empty(_) => Empty(Some(prv2))
        case Branch2(l, v, m, _) => Branch2(l, v, m, Some(prv2))
        case Branch3(l, v1, m, v2, r, _) => Branch3(l, v1, m, v2, r, Some(prv2))
      }
    }

    def +(other: Polynomial) : Polynomial = other match {
      case Empty(_) =>
        val newPrv = useDirectly(plusEmpty, Seq(("t_", lhs), ("s_", rhs), ("u_", other.lhs)), Seq(prv, other.prv))
        updatePrv(newPrv)
      case Branch2(left, value, right, _) =>
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
      case Branch3(left, value1, mid, value2, right, _) =>
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
    }

    def *(x: Monomial) : Polynomial = this match {
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

    def *(other: Polynomial) : Polynomial = this match {
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

    def ^(n: Int) : Polynomial = n match {
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
        } else throw new IllegalArgumentException("negative power unsupported by PolynomialArithV2")
    }

  }

  val varLemmas = (0 until vars.length).map(i => proveBy(Equal(Power(vars(i), "i_()".asTerm),
    Seq(Number(0), Times("1/1".asTerm,
      (0 until vars.length).map(j =>
        if (i == j) Power(vars(i), "i_()".asTerm) else Number(1)).reduceLeft(Times)), Number(0)).reduceLeft(Plus)), QE & done))

  // Constructors
  def Var(index: Int, power: Int) : Polynomial =
    Branch2(Empty(None), Monomial(Coefficient(1, 1),
      (0 until vars.length).map(i => if (i == index) power else 0)), Empty(None), Some(
        varLemmas(index)(USubst(Seq(SubstitutionPair(constR("i_"), Number(power)))))))
  def Var(index: Int) : Polynomial = Var(index, 1)

  val constLemma = rememberAny(
    Equal("n_()".asTerm, Seq(Number(0), Times(Divide(constR("n_"), Number(1)), (0 until vars.length).map(_ => Number(1)).reduceLeft(Times)), Number(0)).reduceLeft(Plus)),
    QE & done)
  val rationalLemma = rememberAny(
    Equal("n_() / d_()".asTerm, Seq(Number(0), Times("n_()/d_()".asTerm, (0 until vars.length).map(_ => Number(1)).reduceLeft(Times)), Number(0)).reduceLeft(Plus)),
    QE & done)
  def Const(num: BigDecimal, denum: BigDecimal) : Polynomial =
    Branch2(Empty(None), Monomial(Coefficient(num, 1, None), (0 until vars.length).map(_ => 0), None), Empty(None),
      Some(rationalLemma(substAny("n_", Number(num))++substAny("d_", Number(denum)))))
  def Const(num: BigDecimal) : Polynomial = Branch2(Empty(None), Monomial(Coefficient(num, 1, None), (0 until vars.length).map(_ => 0), None), Empty(None),
    Some(constLemma(substAny("n_", Number(num)))))

  val One : Polynomial = Const(1)

  case class Empty(prvO: Option[ProvableSig]) extends Polynomial {
    val defaultPrv = zez
    val prv = prvO.getOrElse(defaultPrv)
    override def forgetPrv = Empty(None)
    override def treeSketch: String = "."
  }
  case class Branch2(left: Polynomial, value: Monomial, right: Polynomial, prvO: Option[ProvableSig]) extends Polynomial {
    lazy val defaultPrv = equalReflex(Seq(left.rhs, value.rhs, right.rhs).reduceLeft(Plus))
    // @note detour for "dependent" default argument
    val prv = prvO.getOrElse(defaultPrv)

    override def forgetPrv: Polynomial = Branch2(left, value, right, None)
    override def treeSketch: String = "[" + left.treeSketch + ", " + value.powersString + ", " + right.treeSketch + "]"
  }
  case class Branch3(left: Polynomial, value1: Monomial, mid: Polynomial, value2: Monomial, right: Polynomial, prvO: Option[ProvableSig]) extends Polynomial {
    lazy val defaultPrv = equalReflex(Seq(left.rhs, value1.rhs, mid.rhs, value2.rhs, right.rhs).reduceLeft(Plus))
    // @note detour for "dependent" default argument
    val prv = prvO.getOrElse(defaultPrv)

    override def forgetPrv: Polynomial = Branch3(left, value1, mid, value2, right, None)
    override def treeSketch: String = "{" + left.treeSketch + ", " + value1.powersString + ", " + mid.treeSketch + ", " + value2.powersString + ", " + right.treeSketch + "}"
  }

}
