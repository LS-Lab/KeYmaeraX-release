package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.AntePosition
import org.scalatest.LoneElement._
import edu.cmu.cs.ls.keymaerax.btactics.TaylorModelTactics._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettierPrinter
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.core._
import TactixLibrary._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.BigDecimalQETool

import scala.collection.immutable._

class TaylorModelTests extends TacticTestBase {

  "coarsenTimesBounds" should "work" in withMathematica { _ =>
    proveBy("0 <= t, t <= h(), t*f() <= xRem, xRem <= t*g(), p() ==> q()".asSequent, coarsenTimesBounds("t".asTerm)).
      subgoals.loneElement shouldBe ("0<=t, t<=h(), min((0,h()*f()))<=xRem, xRem<=max((0,h()*g())), p() ==>  q()".asSequent)
  }

  "horner" should "form" in withMathematica { _ =>
    horner("a^2 + 2*a*b + d*b^2 + c + d^3*a*4 + 4".asTerm, "a,b,c".split(",").toList.map(_.asTerm)) shouldBe
      "4+c+b*(b*d)+a*(4*d^3+b*2+a)".asTerm
  }

  "TaylorModel" should "prove the lemma in order 2" in withMathematica { _ =>
    val ode = "{x' = 1 + y, y' = -x^2, t'=1}".asDifferentialProgram
    val tm = TaylorModel(ode, 2).lemma
    tm shouldBe 'proved
    tm.conclusion shouldBe
      """
        |==>
        |((t = 0 & x = a00() * r0() + a01() * r1() + aC0() & y = a10() * r0() + a11() * r1() + aC1()) &
        |  (-1 <= r0() & r0() <= 1) & -1 <= r1() & r1() <= 1) &
        |\forall t
        |  \forall xRem
        |    \forall yRem
        |      (
        |        (0 <= t & t <= h()) &
        |        (min((0,h() * iL0())) <= xRem & xRem <= max((0,h() * iU0()))) &
        |        min((0,h() * iL1())) <= yRem & yRem <= max((0,h() * iU1())) ->
        |        (
        |          iL0() <
        |          yRem +
        |          t *
        |          (r1() * (-2 * (a01() * aC0())) + r0() * (-2 * (a00() * aC0())) + t * (-aC0() + -aC0() * aC1())) &
        |          yRem +
        |          t *
        |          (r1() * (-2 * (a01() * aC0())) + r0() * (-2 * (a00() * aC0())) + t * (-aC0() + -aC0() * aC1())) <
        |          iU0()
        |        ) &
        |        iL1() <
        |        xRem * (-2 * aC0()) + r1() * (xRem * (-2 * a01())) +
        |        r0() * (xRem * (-2 * a00()) + r1() * (-2 * (a00() * a01()))) +
        |        -xRem^2 +
        |        r1()^2 * (-a01()^2) +
        |        r0()^2 * (-a00()^2) +
        |        t *
        |        (
        |          xRem * (-2 + -2 * aC1()) +
        |          r1() * (-2 * a01() + -2 * (a11() * aC0()) + -2 * (a01() * aC1()) + xRem * (-2 * a11())) +
        |          r0() *
        |          (
        |            -2 * a00() + -2 * (a10() * aC0()) + -2 * (a00() * aC1()) + xRem * (-2 * a10()) +
        |            r1() * (-2 * (a01() * a10()) + -2 * (a00() * a11()))
        |          ) +
        |          r1()^2 * (-2 * (a01() * a11())) +
        |          r0()^2 * (-2 * (a00() * a10())) +
        |          t *
        |          (
        |            -1 + -2 * aC1() + -aC1()^2 + aC0()^3 + xRem * aC0()^2 +
        |            r1() * (-2 * a11() + -2 * (a11() * aC1()) + a01() * aC0()^2) +
        |            r0() * (-2 * a10() + -2 * (a10() * aC1()) + a00() * aC0()^2 + r1() * (-2 * (a10() * a11()))) +
        |            r1()^2 * (-a11()^2) +
        |            r0()^2 * (-a10()^2) +
        |            t *
        |            (
        |              aC0()^2 + aC0()^2 * aC1() + r1() * (a11() * aC0()^2) + r0() * (a10() * aC0()^2) +
        |              t * (-1 / 4 * aC0()^4)
        |            )
        |          )
        |        ) &
        |        xRem * (-2 * aC0()) + r1() * (xRem * (-2 * a01())) +
        |        r0() * (xRem * (-2 * a00()) + r1() * (-2 * (a00() * a01()))) +
        |        -xRem^2 +
        |        r1()^2 * (-a01()^2) +
        |        r0()^2 * (-a00()^2) +
        |        t *
        |        (
        |          xRem * (-2 + -2 * aC1()) +
        |          r1() * (-2 * a01() + -2 * (a11() * aC0()) + -2 * (a01() * aC1()) + xRem * (-2 * a11())) +
        |          r0() *
        |          (
        |            -2 * a00() + -2 * (a10() * aC0()) + -2 * (a00() * aC1()) + xRem * (-2 * a10()) +
        |            r1() * (-2 * (a01() * a10()) + -2 * (a00() * a11()))
        |          ) +
        |          r1()^2 * (-2 * (a01() * a11())) +
        |          r0()^2 * (-2 * (a00() * a10())) +
        |          t *
        |          (
        |            -1 + -2 * aC1() + -aC1()^2 + aC0()^3 + xRem * aC0()^2 +
        |            r1() * (-2 * a11() + -2 * (a11() * aC1()) + a01() * aC0()^2) +
        |            r0() * (-2 * a10() + -2 * (a10() * aC1()) + a00() * aC0()^2 + r1() * (-2 * (a10() * a11()))) +
        |            r1()^2 * (-a11()^2) +
        |            r0()^2 * (-a10()^2) +
        |            t *
        |            (
        |              aC0()^2 + aC0()^2 * aC1() + r1() * (a11() * aC0()^2) + r0() * (a10() * aC0()^2) +
        |              t * (-1 / 4 * aC0()^4)
        |            )
        |          )
        |        ) <
        |        iU1()
        |      ) ->
        |[{x'=1 + y, y'=-x^2, t'=1 & 0 <= t & t <= h()}]
        |  (
        |    \exists xRem
        |      (
        |        xRem =
        |        x -
        |        (
        |          aC0() + t + a01() * r1() + a00() * r0() + t * aC1() + t * a11() * r1() + t * a10() * r0() +
        |          -1 / 2 * t^2 * aC0()^2
        |        ) &
        |        t * iL0() <= xRem & xRem <= t * iU0()
        |      ) &
        |    \exists yRem
        |      (
        |        yRem =
        |        y -
        |        (
        |          aC1() + a11() * r1() + a10() * r0() + -1 * t * aC0()^2 + -1 * t^2 * aC0() +
        |          -2 * t * a01() * aC0() * r1() +
        |          -2 * t * a00() * aC0() * r0() +
        |          -1 * t^2 * aC0() * aC1()
        |        ) &
        |        t * iL1() <= yRem & yRem <= t * iU1()
        |      )
        |  )
      """.stripMargin.asSequent
  }

  it should "work for exp" in withMathematica { _ =>
    val ode = "{x' = x, t' = 1}".asDifferentialProgram
    val tm = TaylorModel(ode, 4).lemma
    tm shouldBe 'proved
    tm.conclusion shouldBe
      """
        |==>
        |((t = 0 & x = a00() * r0() + aC0()) &
        |(-1 <= r0() & r0() <= 1)) &
        |\forall t
        |  \forall xRem
        |    (
        |      (0 <= t & t <= h()) & min((0,h() * iL0())) <= xRem & xRem <= max((0,h() * iU0())) ->
        |      iL0() < xRem + t * (t * (t * (r0() * (1 / 6 * a00()) + t * (1 / 24 * aC0())))) &
        |      xRem + t * (t * (t * (r0() * (1 / 6 * a00()) + t * (1 / 24 * aC0())))) < iU0()
        |    ) ->
        |[{x'=x, t'=1 & 0 <= t & t <= h()}]
        |  \exists xRem
        |    (
        |      xRem =
        |      x -
        |      (
        |        aC0() + a00() * r0() + t * aC0() + t * a00() * r0() + 1 / 2 * t^2 * aC0() +
        |        1 / 2 * t^2 * a00() * r0() +
        |        1 / 6 * t^3 * aC0() +
        |        1 / 6 * t^3 * a00() * r0() +
        |        1 / 24 * t^4 * aC0()
        |      ) &
        |      t * iL0() <= xRem & xRem <= t * iU0()
        |    )
      """.stripMargin.asSequent
  }

  it should "prove a lemma about van der Pol" in withMathematica { _ =>
    val ode = "{x' = y, y' = (1 - x^2)*y - x, t' = 1}".asDifferentialProgram
    val tm = TaylorModel(ode, 1).lemma
    tm shouldBe 'proved
  }

  it should "prove a lemma about Lotka-Volterra" in withMathematica { _ =>
    val ode = "{x' = 1.5*x - x*y, y'= -3*y + x*y, t' = 1}".asDifferentialProgram
    val tm = TaylorModel(ode, 2).lemma
    tm shouldBe 'proved
  }

  it should "prove a lemma about Lorenz" in withMathematica { _ =>
    val ode = "{x' = 10 * (y - x), y' = -y*z + 8/3*x - y, z' = x*y - 8/3*z, t' = 1}".asDifferentialProgram
    val tm = TaylorModel(ode, 1).lemma
    tm shouldBe 'proved
  }

  "cutTM" should "cut a Taylor model for exp, sin, cos" in withMathematica { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      val ode = "{x' = x, y' = z, z' = y, t' = 1}".asDifferentialProgram
      val tm = TaylorModel(ode, 6)
      val box = Box(ODESystem(ode, "0 <= t & t <= 0.5".asFormula), "P(x, y, z)".asFormula)
      val assms = ("(t = 0 &" +
        "x = 0.01*r0() + 0*r1() + 0*r2() + 1 &" +
        "y = 0*r0() + 0.01*r1() + 0*r2() + 0.5 &" +
        "z = 0*r0() + 0*r1() + 0.01*r2() + 0) & " +
        "(-1 <= r0() & r0() <= 1) & (-1 <= r1() & r1() <= 1) & (-1 <= r2() & r2() <= 1)").asFormula
      val seq = Sequent(IndexedSeq(assms), IndexedSeq(box))
      val res1 = IntervalArithmeticV2Tests.timing("BigDecimalQETool")(() => proveBy(seq, tm.cutTM(10, AntePosition(1), BigDecimalQETool)(1)))
      val res2 = IntervalArithmeticV2Tests.timing("Mathematica     ")(() => proveBy(seq, tm.cutTM(10, AntePosition(1), qeTool)(1)))
      res1 shouldEqual res2
      val res = proveBy(res1, SimplifierV3.simpTac()(1, 0::1::Nil))
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
          |      \exists xRem
          |        (
          |          xRem =
          |          x -
          |          (
          |            1 + 0.01 * r0() + t + t * 0.01 * r0() + 1 / 2 * t^2 +
          |            1 / 2 * t^2 * 0.01 * r0() +
          |            1 / 6 * t^3 +
          |            1 / 6 * t^3 * 0.01 * r0() +
          |            1 / 24 * t^4 +
          |            1 / 24 * t^4 * 0.01 * r0() +
          |            1 / 120 * t^5 +
          |            1 / 120 * t^5 * 0.01 * r0() +
          |            1 / 720 * t^6
          |          ) &
          |          t * (-5400607643 * 10^-15) <= xRem & xRem <= t * (4880338545 * 10^-14)
          |        ) &
          |      \exists yRem
          |        (
          |          yRem =
          |          y -
          |          (
          |            0.5 + 0.01 * r1() + t * 0.01 * r2() + 1 / 2 * t^2 * 0.5 +
          |            1 / 2 * t^2 * 0.01 * r1() +
          |            1 / 6 * t^3 * 0.01 * r2() +
          |            1 / 24 * t^4 * 0.5 +
          |            1 / 24 * t^4 * 0.01 * r1() +
          |            1 / 120 * t^5 * 0.01 * r2() +
          |            1 / 720 * t^6 * 0.5
          |          ) &
          |          t * (-5364438662 * 10^-15) <= yRem & yRem <= t * (1259823498 * 10^-14)
          |        ) &
          |      \exists zRem
          |        (
          |          zRem =
          |          z -
          |          (
          |            0.01 * r2() + t * 0.5 + t * 0.01 * r1() +
          |            1 / 2 * t^2 * 0.01 * r2() +
          |            1 / 6 * t^3 * 0.5 +
          |            1 / 6 * t^3 * 0.01 * r1() +
          |            1 / 24 * t^4 * 0.01 * r2() +
          |            1 / 120 * t^5 * 0.5 +
          |            1 / 120 * t^5 * 0.01 * r1()
          |          ) &
          |          t * (-5355396416 * 10^-15) <= zRem & zRem <= t * (1982298904 * 10^-14)
          |        )
          |    }
          |  ]
          |    P((x,(y,z)))""".stripMargin.asFormula
    }
  }

  it should "cut a Taylor model for a nonlinear ODE" in withMathematica { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      val ode = "{x' = 1 + y, y' = -x^2, t'=1}".asDifferentialProgram
      val tm = TaylorModel(ode, 2)
      val box = Box(ODESystem(ode, "0 <= t & t <= 0.1".asFormula), "P(x, y, z)".asFormula)
      val assms = ("(t = 0 &" +
        "x = 0.01*r0() + 0*r1() + 1 &" +
        "y = 0*r0() + 0.01*r1() + 0.5) &" +
        "(-1 <= r0() & r0() <= 1) & (-1 <= r1() & r1() <= 1)").asFormula
      val seq = Sequent(IndexedSeq(assms), IndexedSeq(box))
      val res1 = IntervalArithmeticV2Tests.timing("BigDecimalQETool")(() => proveBy(seq, tm.cutTM(10, AntePosition(1), BigDecimalQETool)(1)))
      val res2 = IntervalArithmeticV2Tests.timing("Mathematica     ")(() => proveBy(seq, tm.cutTM(10, AntePosition(1), qeTool)(1)))
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
          |      (0 <= t & t <= 0.1) &
          |      \exists xRem
          |        (
          |          xRem =
          |          x -
          |          (
          |            1 + t + 0 * r1() + 0.01 * r0() + t * 0.5 + t * 0.01 * r1() +
          |            t * 0 * r0() +
          |            -1 / 2 * t^2 * 1^2
          |          ) &
          |          t * (-1887591619 * 10^-11) <= xRem & xRem <= t * (2940096162 * 10^-12)
          |        ) &
          |      \exists yRem
          |        (
          |          yRem =
          |          y -
          |          (
          |            0.5 + 0.01 * r1() + 0 * r0() + -1 * t * 1^2 + -1 * t^2 * 1 +
          |            -2 * t * 0 * 1 * r1() +
          |            -2 * t * 0.01 * 1 * r0() +
          |            -1 * t^2 * 1 * 0.5
          |          ) &
          |          t * (-1875812641 * 10^-11) <= yRem & yRem <= t * (9399926235 * 10^-12)
          |        )
          |    }
          |  ]
          |    P((x,(y,z)))
        """.stripMargin.asFormula
    }
  }
}