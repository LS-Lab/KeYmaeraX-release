/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import org.scalatest.LoneElement._
import edu.cmu.cs.ls.keymaerax.btactics.TaylorModelTactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.AntePosition
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettierPrinter
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettierPrinter
import edu.cmu.cs.ls.keymaerax.tools.ext.BigDecimalTool

import scala.collection.immutable._

@SlowTest
class TaylorModelTests extends TacticTestBase {

  "existsLstable" should "work" in withTactics {
    proveBy("P(), \\exists x Q(x), R() ==> S(), T()".asSequent, existsLstable(-2)).subgoals.loneElement shouldBe
      "P(), Q(x), R()\n  ==>  S(), T()".asSequent
    proveBy("P(x), \\exists x Q(x), R(x,y) ==> S(x, y), T()".asSequent, existsLstable(-2)).subgoals.loneElement shouldBe
      "P(x_0), Q(x), R(x_0,y)\n  ==>  S(x_0,y), T()".asSequent
  }

  "coarsenTimesBounds" should "work" in withMathematica { _ =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      proveBy(
        "0 <= t, t <= h(), t*f() + cL() <= xRem, xRem <= t*g() + cU(), p() ==> q()".asSequent,
        coarsenTimesBounds("t".asTerm),
      ).subgoals.loneElement shouldBe
        ("0<=t, t<=h(), min((0,h()*f()))+cL()<=xRem, xRem<=max((0,h()*g()))+cU(), p() ==>  q()".asSequent)
    }
  }

  "TaylorModel" should "prove the lemma in order 2" in withMathematica { _ =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      val ode = "{x' = 1 + y, y' = -x^2, t'=1}".asDifferentialProgram
      val tm = TaylorModel(ode, 2).lemma
      tm shouldBe Symbol("proved")
      //    println(new KeYmaeraXPrettierPrinter(100).stringify(tm.conclusion))
      tm.conclusion shouldBe
        """
          |==>
          |  (
          |    (t = t0() & x = a00() * r0() + a01() * r1() + aC0() & y = a10() * r0() + a11() * r1() + aC1()) &
          |    (rL0() <= r0() & r0() <= rU0()) & rL1() <= r1() & r1() <= rU1()
          |  ) &
          |  (
          |    (
          |      icL0() <= -tm0e000() + aC0() + r1() * (-tm0e001() + a01()) + r0() * (-tm0e010() + a00()) &
          |      -tm0e000() + aC0() + r1() * (-tm0e001() + a01()) + r0() * (-tm0e010() + a00()) <= icU0()
          |    ) &
          |    icL1() <= -tm1e000() + aC1() + r1() * (-tm1e001() + a11()) + r0() * (-tm1e010() + a10()) &
          |    -tm1e000() + aC1() + r1() * (-tm1e001() + a11()) + r0() * (-tm1e010() + a10()) <= icU1()
          |  ) &
          |  \forall s
          |    \forall Rem0
          |      \forall Rem1
          |        (
          |          (0 <= s & s <= h()) &
          |          (min((0,h() * iL0())) + icL0() <= Rem0 & Rem0 <= max((0,h() * iU0())) + icU0()) &
          |          min((0,h() * iL1())) + icL1() <= Rem1 & Rem1 <= max((0,h() * iU1())) + icU1() ->
          |          (
          |            iL0() <
          |            1 + tm1e000() + -tm0e100() + Rem1 + r1() * (tm1e001() + -tm0e101()) +
          |            r0() * (tm1e010() + -tm0e110()) +
          |            s *
          |            (tm1e100() + (-2) * tm0e200() + r1() * tm1e101() + r0() * tm1e110() + s * tm1e200()) &
          |            1 + tm1e000() + -tm0e100() + Rem1 + r1() * (tm1e001() + -tm0e101()) +
          |            r0() * (tm1e010() + -tm0e110()) +
          |            s *
          |            (tm1e100() + (-2) * tm0e200() + r1() * tm1e101() + r0() * tm1e110() + s * tm1e200()) <
          |            iU0()
          |          ) &
          |          iL1() <
          |          -tm1e100() + -tm0e000()^2 + Rem0 * ((-2) * tm0e000()) +
          |          r1() * (-tm1e101() + (-2) * tm0e000() * tm0e001() + Rem0 * ((-2) * tm0e001())) +
          |          r0() *
          |          (
          |            -tm1e110() + (-2) * tm0e000() * tm0e010() + Rem0 * ((-2) * tm0e010()) +
          |            r1() * ((-2) * tm0e001() * tm0e010())
          |          ) +
          |          -Rem0^2 +
          |          r1()^2 * (-tm0e001()^2) +
          |          r0()^2 * (-tm0e010()^2) +
          |          s *
          |          (
          |            (-2) * tm1e200() + (-2) * tm0e000() * tm0e100() + Rem0 * ((-2) * tm0e100()) +
          |            r1() *
          |            (
          |              (-2) * tm0e000() * tm0e101() + (-2) * tm0e001() * tm0e100() +
          |              Rem0 * ((-2) * tm0e101())
          |            ) +
          |            r0() *
          |            (
          |              (-2) * tm0e000() * tm0e110() + (-2) * tm0e010() * tm0e100() +
          |              Rem0 * ((-2) * tm0e110()) +
          |              r1() * ((-2) * tm0e001() * tm0e110() + (-2) * tm0e010() * tm0e101())
          |            ) +
          |            r1()^2 * ((-2) * tm0e001() * tm0e101()) +
          |            r0()^2 * ((-2) * tm0e010() * tm0e110()) +
          |            s *
          |            (
          |              (-2) * tm0e000() * tm0e200() + -tm0e100()^2 + Rem0 * ((-2) * tm0e200()) +
          |              r1() * ((-2) * tm0e001() * tm0e200() + (-2) * tm0e100() * tm0e101()) +
          |              r0() *
          |              (
          |                (-2) * tm0e010() * tm0e200() + (-2) * tm0e100() * tm0e110() +
          |                r1() * ((-2) * tm0e101() * tm0e110())
          |              ) +
          |              r1()^2 * (-tm0e101()^2) +
          |              r0()^2 * (-tm0e110()^2) +
          |              s *
          |              (
          |                (-2) * tm0e100() * tm0e200() + r1() * ((-2) * tm0e101() * tm0e200()) +
          |                r0() * ((-2) * tm0e110() * tm0e200()) +
          |                s * (-tm0e200()^2)
          |              )
          |            )
          |          ) &
          |          -tm1e100() + -tm0e000()^2 + Rem0 * ((-2) * tm0e000()) +
          |          r1() * (-tm1e101() + (-2) * tm0e000() * tm0e001() + Rem0 * ((-2) * tm0e001())) +
          |          r0() *
          |          (
          |            -tm1e110() + (-2) * tm0e000() * tm0e010() + Rem0 * ((-2) * tm0e010()) +
          |            r1() * ((-2) * tm0e001() * tm0e010())
          |          ) +
          |          -Rem0^2 +
          |          r1()^2 * (-tm0e001()^2) +
          |          r0()^2 * (-tm0e010()^2) +
          |          s *
          |          (
          |            (-2) * tm1e200() + (-2) * tm0e000() * tm0e100() + Rem0 * ((-2) * tm0e100()) +
          |            r1() *
          |            (
          |              (-2) * tm0e000() * tm0e101() + (-2) * tm0e001() * tm0e100() +
          |              Rem0 * ((-2) * tm0e101())
          |            ) +
          |            r0() *
          |            (
          |              (-2) * tm0e000() * tm0e110() + (-2) * tm0e010() * tm0e100() +
          |              Rem0 * ((-2) * tm0e110()) +
          |              r1() * ((-2) * tm0e001() * tm0e110() + (-2) * tm0e010() * tm0e101())
          |            ) +
          |            r1()^2 * ((-2) * tm0e001() * tm0e101()) +
          |            r0()^2 * ((-2) * tm0e010() * tm0e110()) +
          |            s *
          |            (
          |              (-2) * tm0e000() * tm0e200() + -tm0e100()^2 + Rem0 * ((-2) * tm0e200()) +
          |              r1() * ((-2) * tm0e001() * tm0e200() + (-2) * tm0e100() * tm0e101()) +
          |              r0() *
          |              (
          |                (-2) * tm0e010() * tm0e200() + (-2) * tm0e100() * tm0e110() +
          |                r1() * ((-2) * tm0e101() * tm0e110())
          |              ) +
          |              r1()^2 * (-tm0e101()^2) +
          |              r0()^2 * (-tm0e110()^2) +
          |              s *
          |              (
          |                (-2) * tm0e100() * tm0e200() + r1() * ((-2) * tm0e101() * tm0e200()) +
          |                r0() * ((-2) * tm0e110() * tm0e200()) +
          |                s * (-tm0e200()^2)
          |              )
          |            )
          |          ) <
          |          iU1()
          |        ) ->
          |  [{x'=1 + y, y'=-x^2, t'=1 & t0() <= t & t <= t0() + h()}]
          |    \exists s
          |      (
          |        (t = t0() + s & 0 <= s & s <= h()) &
          |        \exists Rem0
          |          (
          |            x =
          |            tm0e000() + tm0e010() * r0() + tm0e001() * r1() + tm0e100() * s +
          |            tm0e101() * (s * r1()) +
          |            tm0e200() * s^2 +
          |            tm0e110() * (s * r0()) +
          |            Rem0 &
          |            s * iL0() + icL0() <= Rem0 & Rem0 <= s * iU0() + icU0()
          |          ) &
          |        \exists Rem1
          |          (
          |            y =
          |            tm1e000() + tm1e010() * r0() + tm1e001() * r1() + tm1e100() * s +
          |            tm1e101() * (s * r1()) +
          |            tm1e200() * s^2 +
          |            tm1e110() * (s * r0()) +
          |            Rem1 &
          |            s * iL1() + icL1() <= Rem1 & Rem1 <= s * iU1() + icU1()
          |          )
          |      )
      """.stripMargin.asSequent
    }
  }

  it should "work for exp" in withMathematica { _ =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      val ode = "{x' = x, t' = 1}".asDifferentialProgram
      val tm = TaylorModel(ode, 4).lemma
      tm shouldBe Symbol("proved")
      // println(new KeYmaeraXPrettierPrinter(100).stringify(tm.conclusion))
      tm.conclusion shouldBe
        """
          |==>
          |((t = t0() & x = a00() * r0() + aC0()) & rL0() <= r0() & r0() <= rU0()) &
          |  (
          |    icL0() <= -tm0e00() + aC0() + r0() * (-tm0e01() + a00()) &
          |    -tm0e00() + aC0() + r0() * (-tm0e01() + a00()) <= icU0()
          |  ) &
          |  \forall s
          |    \forall Rem0
          |      (
          |        (0 <= s & s <= h()) &
          |        min((0,h() * iL0())) + icL0() <= Rem0 & Rem0 <= max((0,h() * iU0())) + icU0() ->
          |        iL0() <
          |        -tm0e10() + tm0e00() + Rem0 + r0() * (-tm0e11() + tm0e01()) +
          |        s *
          |        (
          |          (-2) * tm0e20() + tm0e10() + r0() * ((-2) * tm0e21() + tm0e11()) +
          |          s *
          |          (
          |            (-3) * tm0e30() + tm0e20() + r0() * ((-3) * tm0e31() + tm0e21()) +
          |            s * ((-4) * tm0e40() + tm0e30() + r0() * tm0e31() + s * tm0e40())
          |          )
          |        ) &
          |        -tm0e10() + tm0e00() + Rem0 + r0() * (-tm0e11() + tm0e01()) +
          |        s *
          |        (
          |          (-2) * tm0e20() + tm0e10() + r0() * ((-2) * tm0e21() + tm0e11()) +
          |          s *
          |          (
          |            (-3) * tm0e30() + tm0e20() + r0() * ((-3) * tm0e31() + tm0e21()) +
          |            s * ((-4) * tm0e40() + tm0e30() + r0() * tm0e31() + s * tm0e40())
          |          )
          |        ) <
          |        iU0()
          |      ) ->
          |  [{x'=x, t'=1 & t0() <= t & t <= t0() + h()}]
          |    \exists s
          |      (
          |        (t = t0() + s & 0 <= s & s <= h()) &
          |        \exists Rem0
          |          (
          |            x =
          |            tm0e00() + tm0e01() * r0() + tm0e10() * s + tm0e11() * (s * r0()) + tm0e20() * s^2 +
          |            tm0e21() * (s^2 * r0()) +
          |            tm0e30() * s^3 +
          |            tm0e31() * (s^3 * r0()) +
          |            tm0e40() * s^4 +
          |            Rem0 &
          |            s * iL0() + icL0() <= Rem0 & Rem0 <= s * iU0() + icU0()
          |          )
          |      )
      """.stripMargin.asSequent
    }
  }


  it should "prove a lemma about van der Pol" in withMathematica { _ =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      val vdp = "{x' = y, y' = (1 - x^2)*y - x,t'=1}".asDifferentialProgram
      val tm = TaylorModel(vdp, 1).lemma
      tm shouldBe Symbol("proved")
    }
  }

  it should "prove a lemma about parametrized van der Pol" in withMathematica { _ =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      val tm = TaylorModel("{x' = y, y' = m()*(1 - x^2)*y - x,t'=1}".asDifferentialProgram, 1)
      tm.lemma shouldBe Symbol("proved")
      tm.timestepLemma shouldBe Symbol("proved")
    }
  }

  it should "prove a lemma about coupled van der Pol" in
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      withMathematica { _ =>
        val cvdp =
          "{x1' = y1, y1' = (1-x1^2)*y1 + b()*(x2-x1) - x1, x2' = y2, y2' = (1-x2^2)*y2 - b()*(x2-x1) - x2, t'=1}"
            .asDifferentialProgram
        val tm = TaylorModel(cvdp, 1)
        tm.lemma shouldBe Symbol("proved")
        tm.timestepLemma shouldBe Symbol("proved")
      }
    }

  it should "prove a lemma about Lotka-Volterra" in withMathematica { _ =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      val ode = "{x' = 1.5*x - x*y, y'= -3*y + x*y, t' = 1}".asDifferentialProgram
      val tm = TaylorModel(ode, 2).lemma
      tm shouldBe Symbol("proved")
    }
  }

  it should "prove a lemma about Lorenz" in withMathematica { _ =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      val ode = "{x' = 10 * (y - x), y' = -y*z + 8/3*x - y, z' = x*y - 8/3*z, t' = 1}".asDifferentialProgram
      val tm = TaylorModel(ode, 1).lemma
      tm shouldBe Symbol("proved")
    }
  }

  "cutTM" should "cut a Taylor model for exp, sin, cos" in withMathematica { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      val ode = "{x' = x, y' = z, z' = y, t' = 1}".asDifferentialProgram
      val tm = TaylorModel(ode, 6)
      val box = Box(ODESystem(ode, "0 <= t & t <= 0 + 0.5".asFormula), "P(x, y, z)".asFormula)
      val assms =
        ("(t = 0 &" + "x = 0.01*r0() + 0*r1() + 0*r2() + 1 &" + "y = 0*r0() + 0.01*r1() + 0*r2() + 0.5 &" +
          "z = 0*r0() + 0*r1() + 0.01*r2() + 0) & " +
          "(-1 <= r0() & r0() <= 1) & (-1 <= r1() & r1() <= 1) & (-1 <= r2() & r2() <= 1)").asFormula
      val seq = Sequent(IndexedSeq(assms), IndexedSeq(box))
      val bgtool = new BigDecimalTool()
      bgtool.init(Map.empty)
      val res1 = IntervalArithmeticV2Tests
        .timing("BigDecimalQETool")(() => proveBy(seq, tm.cutTM(10, AntePosition(1), bgtool)(1)))
      val res2 = IntervalArithmeticV2Tests
        .timing("Mathematica     ")(() => proveBy(seq, tm.cutTM(10, AntePosition(1), qeTool)(1)))
      res1 shouldEqual res2
      val res = proveBy(res1, SimplifierV3.simpTac()(1, 0 :: 1 :: Nil))
      // println(new KeYmaeraXPrettierPrinter(80).stringify(res.subgoals.loneElement))
      res.subgoals.loneElement.ante.loneElement shouldBe assms
      res.subgoals.loneElement.succ.loneElement shouldBe
        """[
          |    {
          |      x'=x,
          |      y'=z,
          |      z'=y,
          |      t'=1 &
          |      (0 <= t & t <= 0.5) &
          |      \exists s
          |        (
          |          (t = s & 0 <= s & s <= 0.5) &
          |          \exists Rem0
          |            (
          |              x =
          |              1 + 0.01 * r0() + s + 0.01 * (s * r0()) + 0.5 * s^2 +
          |              0.16666666665 * s^3 +
          |              0.005 * (s^2 * r0()) +
          |              0.0016666666665 * (s^3 * r0()) +
          |              0.041666666665 * s^4 +
          |              0.0083333333335 * s^5 +
          |              0.00041666666665 * (s^4 * r0()) +
          |              0.0013888888885 * s^6 +
          |              0.000083333333335 * (s^5 * r0()) +
          |              Rem0 &
          |              s * ((-523314372) * 10^(-14)) <= Rem0 &
          |              Rem0 <= s * (486364251 * 10^(-13))
          |            ) &
          |          \exists Rem1
          |            (
          |              y =
          |              0.5 + 0.01 * r1() + 0.25 * s^2 + 0.01 * (s * r2()) +
          |              0.005 * (s^2 * r1()) +
          |              0.0016666666665 * (s^3 * r2()) +
          |              0.020833333335 * s^4 +
          |              0.00041666666665 * (s^4 * r1()) +
          |              0.000083333333335 * (s^5 * r2()) +
          |              0.00069444444425 * s^6 +
          |              Rem1 &
          |              s * ((-522695019) * 10^(-14)) <= Rem1 &
          |              Rem1 <= s * (124607299 * 10^(-13))
          |            ) &
          |          \exists Rem2
          |            (
          |              z =
          |              0.01 * r2() + 0.5 * s + 0.01 * (s * r1()) + 0.083333333325 * s^3 +
          |              0.005 * (s^2 * r2()) +
          |              0.0016666666665 * (s^3 * r1()) +
          |              0.0041666666665 * s^5 +
          |              0.00041666666665 * (s^4 * r2()) +
          |              0.000083333333335 * (s^5 * r1()) +
          |              Rem2 &
          |              s * ((-522822616) * 10^(-14)) <= Rem2 &
          |              Rem2 <= s * (196958106 * 10^(-13))
          |            )
          |        )
          |    }
          |  ]
          |    P((x,y,z))""".stripMargin.asFormula
    }
  }

  it should "cut a Taylor model for a nonlinear ODE" in withMathematica { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      val ode = "{x' = 1 + y, y' = -x^2, t'=1}".asDifferentialProgram
      val tm = TaylorModel(ode, 2)
      val box = Box(ODESystem(ode, "0 <= t & t <= 0 + 0.1".asFormula), "P(x, y, z)".asFormula)
      val assms =
        ("(t = 0 &" + "x = 0.01*r0() + 0*r1() + 1 &" + "y = 0*r0() + 0.01*r1() + 0.5) &" +
          "(-1 <= r0() & r0() <= 1) & (-1 <= r1() & r1() <= 1)").asFormula
      val seq = Sequent(IndexedSeq(assms), IndexedSeq(box))
      val bgtool = new BigDecimalTool()
      bgtool.init(Map.empty)
      val res1 = IntervalArithmeticV2Tests
        .timing("BigDecimalQETool")(() => proveBy(seq, tm.cutTM(10, AntePosition(1), bgtool)(1)))
      val res2 = IntervalArithmeticV2Tests
        .timing("Mathematica     ")(() => proveBy(seq, tm.cutTM(10, AntePosition(1), qeTool)(1)))
      res1 shouldEqual res2
      val res = res1
      // println(new KeYmaeraXPrettierPrinter(80).stringify(res.subgoals.loneElement))
      res.subgoals.loneElement.ante.loneElement shouldBe assms
      res.subgoals.loneElement.succ.loneElement shouldBe
        """[
          |    {
          |      x'=1 + y,
          |      y'=-x^2,
          |      t'=1 &
          |      (0 <= t & t <= 0 + 0.1) &
          |      \exists s
          |        (
          |          (t = 0 + s & 0 <= s & s <= 0.1) &
          |          \exists Rem0
          |            (
          |              x =
          |              1 + 0.01 * r0() + 0 * r1() + 1.5 * s + 0.01 * (s * r1()) +
          |              (-0.5) * s^2 +
          |              0 * (s * r0()) +
          |              Rem0 &
          |              s * ((-189040551) * 10^(-10)) + 0.00 <= Rem0 &
          |              Rem0 <= s * (296823505 * 10^(-11)) + 0.00
          |            ) &
          |          \exists Rem1
          |            (
          |              y =
          |              0.5 + 0 * r0() + 0.01 * r1() + (-1) * s + 0 * (s * r1()) +
          |              (-1.5) * s^2 +
          |              (-0.02) * (s * r0()) +
          |              Rem1 &
          |              s * ((-188091640) * 10^(-10)) + 0.00 <= Rem1 &
          |              Rem1 <= s * (945066145 * 10^(-11)) + 0.00
          |            )
          |        )
          |    }
          |  ]
          |    P((x,y,z))
        """.stripMargin.asFormula
    }
  }

  "Taylor model time step lemma" should "work with low order sin,cos" in withMathematica { _ =>
    val pp = new KeYmaeraXPrettierPrinter(100)
    val ode = "{x' = y, y' = -x, t'=1}".asDifferentialProgram
    val tm = TaylorModel(ode, 1)
    val tslemma = tm.timestepLemma
    println(pp.stringify(tslemma))
    tslemma shouldBe Symbol("proved")
    tslemma.conclusion.ante shouldBe Symbol("empty")
    tslemma.conclusion.succ.loneElement shouldBe
      """    (
        |      (
        |        (
        |          (
        |            (
        |              t = t0() &
        |              x = a00() * r0() + a01() * r1() + aC0() & y = a10() * r0() + a11() * r1() + aC1()
        |            ) &
        |            (rL0() <= r0() & r0() <= rU0()) & rL1() <= r1() & r1() <= rU1()
        |          ) &
        |          (
        |            (
        |              icL0() <=
        |              -tm0e000() + aC0() + r1() * (-tm0e001() + a01()) + r0() * (-tm0e010() + a00()) &
        |              -tm0e000() + aC0() + r1() * (-tm0e001() + a01()) + r0() * (-tm0e010() + a00()) <=
        |              icU0()
        |            ) &
        |            icL1() <=
        |            -tm1e000() + aC1() + r1() * (-tm1e001() + a11()) + r0() * (-tm1e010() + a10()) &
        |            -tm1e000() + aC1() + r1() * (-tm1e001() + a11()) + r0() * (-tm1e010() + a10()) <= icU1()
        |          ) &
        |          \forall s
        |            \forall Rem0
        |              \forall Rem1
        |                (
        |                  (0 <= s & s <= h()) &
        |                  (min(0,h() * iL0()) + icL0() <= Rem0 & Rem0 <= max(0,h() * iU0()) + icU0()) &
        |                  min(0,h() * iL1()) + icL1() <= Rem1 & Rem1 <= max(0,h() * iU1()) + icU1() ->
        |                  (
        |                    iL0() <
        |                    tm1e000() + -tm0e100() + Rem1 + r1() * tm1e001() + r0() * tm1e010() +
        |                    s * tm1e100() &
        |                    tm1e000() + -tm0e100() + Rem1 + r1() * tm1e001() + r0() * tm1e010() +
        |                    s * tm1e100() <
        |                    iU0()
        |                  ) &
        |                  iL1() <
        |                  -tm1e100() + -tm0e000() + -Rem0 + r1() * (-tm0e001()) + r0() * (-tm0e010()) +
        |                  s * (-tm0e100()) &
        |                  -tm1e100() + -tm0e000() + -Rem0 + r1() * (-tm0e001()) + r0() * (-tm0e010()) +
        |                  s * (-tm0e100()) <
        |                  iU1()
        |                )
        |        ) &
        |        0 <= h()
        |      ) &
        |      \forall s
        |        \forall x
        |          \forall y
        |            (
        |              (0 <= s & s <= h()) &
        |              \exists Rem0
        |                (
        |                  x = tm0e000() + tm0e001() * r1() + tm0e010() * r0() + tm0e100() * s + Rem0 &
        |                  s * iL0() + icL0() <= Rem0 & Rem0 <= s * iU0() + icU0()
        |                ) &
        |              \exists Rem1
        |                (
        |                  y = tm1e000() + tm1e001() * r1() + tm1e010() * r0() + tm1e100() * s + Rem1 &
        |                  s * iL1() + icL1() <= Rem1 & Rem1 <= s * iU1() + icU1()
        |                ) ->
        |              P_(x,y,t + s)
        |            )
        |    ) &
        |    \forall t
        |      \forall x
        |        \forall y
        |          (
        |            t = t0() + h() &
        |            \exists Rem0
        |              (
        |                x = tm0e000() + tm0e001() * r1() + tm0e010() * r0() + tm0e100() * h() + Rem0 &
        |                h() * iL0() + icL0() <= Rem0 & Rem0 <= h() * iU0() + icU0()
        |              ) &
        |            \exists Rem1
        |              (
        |                y = tm1e000() + tm1e001() * r1() + tm1e010() * r0() + tm1e100() * h() + Rem1 &
        |                h() * iL1() + icL1() <= Rem1 & Rem1 <= h() * iU1() + icU1()
        |              ) ->
        |            [{x'=y, y'=-x, t'=1}]P_(x,y,t)
        |          ) ->
        |    [{x'=y, y'=-x, t'=1}]P_(x,y,t)""".stripMargin.asFormula
  }

  it should "work with higher order sin,cos,exp" in withMathematica { _ =>
    val pp = new KeYmaeraXPrettierPrinter(100)
    val ode = "{x' = y, y' = -x, z'=z, t'=1}".asDifferentialProgram
    val tm = TaylorModel(ode, 3)
    val tslemma = tm.timestepLemma
    tslemma shouldBe Symbol("proved")
    // println(pp.stringify(tslemma))
  }

  it should "work with van der Pol" in withMathematica { _ =>
    val pp = new KeYmaeraXPrettierPrinter(100)
    val vdp = "{x' = y, y' = (1 - x^2)*y - x,t'=1}".asDifferentialProgram
    val tm = TaylorModel(vdp, 3)
    val tslemma = tm.timestepLemma
    tslemma shouldBe Symbol("proved")
    // println(pp.stringify(tslemma))
  }

  "big StaticSingleAssignmentExpression" should "be constructed in a reasonable amount of time" in withMathematica {
    _ =>
      withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
        import Timing._
        val tm = TaylorModel("{x' = y, y' = (1 - x^2)*y - x,t'=1}".asDifferentialProgram, 4)
        tic()
        val ssa = new IntervalArithmeticV2.StaticSingleAssignmentExpression(tm.innerNumbericCondition)
        toc("StaticSingleAssignmentExpression constructed")
        println(ssa.unfoldMap.toList.length)
      }
  }

}
