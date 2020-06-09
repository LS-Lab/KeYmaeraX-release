package btactics

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettierPrinter
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.KeYmaeraXTestTags.SlowTest
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.infrastruct.{PosInExpr, SuccPosition}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.ext.{BigDecimalTool, RingsLibrary}
import edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool

import scala.collection.immutable._
import org.scalatest.LoneElement._

/**
  * @author Fabian Immler
  */
class TaylorModelArithTests extends TacticTestBase {

  import PolynomialArithV2._
  import PolynomialArithV2Helpers._

  val context3 = ("-1 <= x0(), x0() <= 1, -1 <= y0(), y0() <= 1, -1 <= z0(), z0() <= 1," +
    "x = x0() + y0() + rx, -0.01 <= rx, rx <= 0.02," +
    "y = 0.5*x0() - y0() + ry, 0 <= ry, ry <= 0.1").split(',').map(_.asFormula).toIndexedSeq
  implicit val defaultOptions = new TaylorModelOptions {
    override val precision = 5
    override val order = 4
  }
  implicit val defaultTimeStepOptions = new TimeStepOptions {
    def remainderEstimation(i: Integer) = (0.0001, 0.0001)
  }
  lazy val tma = new TaylorModelArith()
  lazy val x0 = ring.ofTerm("x0()".asTerm)
  lazy val y0 = ring.ofTerm("y0()".asTerm)
  lazy val tm1 = tma.TM("x".asTerm, x0 + y0, "-0.01".asTerm, "0.02".asTerm, context3, QE)
  lazy val tm2 = tma.TM("y".asTerm, ring.Const(BigDecimal("0.5")) * x0 - y0, "0".asTerm, "0.1".asTerm, context3, QE)
  lazy val third = tma.Exact(ring.ofTerm("1/3".asTerm), context3)
  lazy val tm3 = third *! tm1
  lazy val tm100000 = tma.Exact(ring.ofTerm("0.000001".asTerm), context3) *! tm1
  lazy val tm1234 = tma.Exact(ring.ofTerm("12.34".asTerm), context3) *! tm2

  "Taylor models" should "add exactly" in withMathematica { qeTool =>
    (tm1 +! tm2).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x+y=1.5*x0()+err_&-0.01<=err_&err_<=0.12)".asFormula
  }

  it should "add approximately" in withMathematica { qeTool =>
    (tm1 +! tm100000).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x+0.000001*x=1.000001*x0()+1.000001*y0()+err_&-0.010001<=err_&err_<=0.020001)".asFormula
    (tm1 + tm100000).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x+0.000001*x=x0()+y0()+err_&-0.010003<=err_&err_<=0.020003)".asFormula
  }

  it should "subtract exactly" in withMathematica { qeTool =>
    (tm1 -! tm2).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x-y=0.5*x0()+2*y0()+err_&-0.11<=err_&err_<=0.02)".asFormula
  }

  it should "subtract approximately" in withMathematica { qeTool =>
    (tm1 -! tm100000).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x-0.000001*x=0.999999*x0()+0.999999*y0()+err_&-0.010001<=err_&err_<=0.020001)".asFormula
    (tm1 - tm100000).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x-0.000001*x=0.9999*x0()+0.9999*y0()+err_&-0.010199<=err_&err_<=0.020199)".asFormula
  }

  it should "multiply exactly" in withMathematica { qeTool =>
    (tm1 *! tm2).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x*y=0.5*x0()^2+- 0.5*x0()*y0()+- y0()^2+err_&-0.231<=err_&err_<=0.232)".asFormula
  }

  it should "multiply approximately" in withMathematica { qeTool =>
    (tm1234 *! tm1234).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (12.34*y*(12.34*y)=38.068900*x0()^2+- 152.27560*x0()*y0()+152.2756*y0()^2+err_&-45.684<=err_&err_<=47.207)".asFormula
    (tm1234 * tm1234).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (12.34*y*(12.34*y)=38.06*x0()^2+- 152.3*x0()*y0()+152.2*y0()^2+err_&-45.793<=err_&err_<=47.316)".asFormula
  }

  it should "negate" in withMathematica { qeTool =>
    (-tm1).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (-x=-x0()+- y0()+err_&-0.02<=err_&err_<=0.01)".asFormula
  }

  it should "square exactly" in withMathematica { qeTool =>
    tm1.squareExact.prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x^2=x0()^2+2*x0()*y0()+y0()^2+err_&-0.08<=err_&err_<=0.0804)".asFormula
  }

  it should "square approximately" in withMathematica { qeTool =>
    tm1234.squareExact.prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ ((12.34*y)^2=38.068900*x0()^2+- 152.27560*x0()*y0()+152.2756*y0()^2+err_&-45.683<=err_&err_<=47.206)".asFormula
    tm1234.square.prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ ((12.34*y)^2=38.06*x0()^2+- 152.3*x0()*y0()+152.2*y0()^2+err_&-45.792<=err_&err_<=47.315)".asFormula
  }

  it should "^1" in withMathematica { qeTool =>
    (tm1^1).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x^1=x0()+y0()+err_&-0.01<=err_&err_<=0.02)".asFormula
  }

  it should "^(2*n)" in withMathematica { qeTool =>
    (tm1^4).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x^4=x0()^4+4*x0()^3*y0()+6*x0()^2*y0()^2+4*x0()*y0()^3+y0()^4+err_&-0.64<=err_&err_<=0.64967)".asFormula
  }
  it should "^(2*n + 1)" in withMathematica { qeTool =>
    (tm1^3).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x^3=x0()^3+3*x0()^2*y0()+3*x0()*y0()^2+y0()^3+err_&-0.2024<=err_&err_<=0.24241)".asFormula
  }

  it should "exponentiate approximately" in withMathematica { qeTool =>
    (tm1234^3).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ ((12.34*y)^3=234.8*x0()^3+- 1410*x0()^2*y0()+2818*x0()*y0()^2+- 1879*y0()^3+err_&-1122.4<=err_&err_<=1359.0)".asFormula
  }

  it should "exact" in withMathematica { qeTool =>
    import tma._
    import ring._
    val a = ofTerm("x0()".asTerm)
    val b = ofTerm("1".asTerm)
    val c = ofTerm("1/3".asTerm)
    val tmA = Exact(a, context3)
    val tmB = Exact(b, context3)
    val tmC = Exact(c, context3)
    (tmA).prettyPrv.conclusion.succ(0) shouldBe "\\exists err_ (x0()=x0()+err_&0<=err_&err_<=0)".asFormula
    (tmB).prettyPrv.conclusion.succ(0) shouldBe "\\exists err_ (1=1+err_&0<=err_&err_<=0)".asFormula
    (tmC).prettyPrv.conclusion.succ(0) shouldBe "\\exists err_ (1/3=1/3+err_&0<=err_&err_<=0)".asFormula
  }

  it should "approx" in withMathematica { qeTool =>
    val tm = (tm3 +! tm2).squareExact
    val tmA = tm.approx
    tmA.prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ ((1/3*x+y)^2=0.6944*x0()^2+- 1.112*x0()*y0()+0.4444*y0()^2+err_&-0.32102<=err_&err_<=0.33240)".asFormula
  }

  it should "form Horner" in withMathematica { qeTool =>
    import tma._
    import ring._
    val hornerPrv = toHorner(ofTerm("(x0()+y0()+z0())^2".asTerm))
    hornerPrv shouldBe 'proved
    hornerPrv.conclusion.ante shouldBe 'empty
    hornerPrv.conclusion.succ.loneElement shouldBe
      "(x0()+y0()+z0())^2=z0()*z0()+y0()*(z0()*2+y0())+x0()*(z0()*2+y0()*2+x0())".asFormula
  }

  it should "collect higher order terms" in withMathematica { qeTool =>
    import tma._
    import ring._
    val tm = (tm3 + tm2 + third) ^ 3
    val res0 = tm.collectHigherOrderTerms(new TaylorModelOptions { val precision = defaultOptions.precision; val order = 0})
    val res1 = tm.collectHigherOrderTerms(new TaylorModelOptions { val precision = defaultOptions.precision; val order = 1})
    res0.prettyPrv.conclusion.succ.loneElement shouldBe
      "\\exists err_ ((1/3*x+y+1/3)^3=0.03699+err_&(-6.8403)<=err_&err_<=7.2716)".asFormula
    res1.prettyPrv.conclusion.succ.loneElement shouldBe
      "\\exists err_ ((1/3*x+y+1/3)^3=0.2776*x0()+-(0.2222*y0())+0.03699+err_&(-6.3405)<=err_&err_<=6.7718)".asFormula
  }

  it should "interval" in withMathematica { qeTool =>
    import tma._
    import ring._
    val tm = (tm3 + tm2 + third) ^ 3
    tm.interval._1 shouldBe "(-68034)*10^(-4)".asTerm
    tm.interval._2 shouldBe "73086*10^(-4)".asTerm
    tm.interval._3.conclusion.succ.loneElement shouldBe
      "(-68034)*10^(-4)<=(1/3*x+y+1/3)^3&(1/3*x+y+1/3)^3<=73086*10^(-4)".asFormula
  }

  it should "drop empty interval" in withMathematica { qeTool =>
    val context = IndexedSeq("x = 1.4 + 0.15 * e0".asFormula)
    val x = tma.TM("x".asTerm, ring.ofTerm("1.4 + 0.15 * e0".asTerm), Number(0), Number(0), context, QE)
    x.dropEmptyInterval.get.conclusion.succ.loneElement shouldBe "x=0+0.15/1*(1*e0^1)+0+1.4/1*1+0".asFormula
  }

  "timeStep" should "van der Pol" in withMathematica { qeTool =>
    withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
      // TODO: generate a context like this from "x : [1.25, 1.55]" and "y : [2.35, 2.45]"?!
      val context = "t = 0, x = 1.4 + 0.15 * e0, y = 2.4 + 0.05 * e1, -1 <= e0, e0 <= 1, -1 <= e1, e1 <= 1".split(',').map(_.asFormula).toIndexedSeq
      val vdp = new tma.TemplateLemmas("{x' = y, y' = (1 - x^2)*y - x,t'=1}".asDifferentialProgram, 3)
      val x = tma.TM("x".asTerm, ring.ofTerm("1.4 + 0.15 * e0".asTerm), Number(0), Number(0), context, QE)
      val y = tma.TM("y".asTerm, ring.ofTerm("2.4 + 0.05 * e1".asTerm), Number(0), Number(0), context, QE)
      val r0 = tma.TM("e0".asTerm, ring.ofTerm("e0".asTerm), Number(0), Number(0), context, QE)
      val r1 = tma.TM("e1".asTerm, ring.ofTerm("e1".asTerm), Number(0), Number(0), context, QE)
      val t = proveBy(Sequent(context, IndexedSeq("t = 0".asFormula)), closeId)
      val res = vdp.timeStepPreconditionedODE(Seq(x, y), Seq(r0, r1), t, 0.01)
      // println(new KeYmaeraXPrettierPrinter(100).stringify(res.conclusion.succ.loneElement))
      res.conclusion.succ.loneElement shouldBe
        """[{x'=y, y'=(1 - x^2) * y - x, t'=1 & 0 <= t & t <= 0 + 0.01}]
          |  \exists s
          |    (
          |      (t = 0 + s & 0 <= s & s <= 0.01) &
          |      \exists Rem0
          |        (
          |          x =
          |          1.4 + 0.15 * e0 + 0 * e1 + 2.4 * s + 0.05 * (s * e1) + (-1.8520) * s^2 + 0 * (s * e0) +
          |          (-0.02400) * (s^2 * e1) +
          |          (-2.4954) * s^3 +
          |          (-0.5790) * (s^2 * e0) +
          |          Rem0 &
          |          s * ((-8724) * 10^(-7)) + 0.00 <= Rem0 & Rem0 <= s * (4131 * 10^(-7)) + 0.00
          |        ) &
          |      \exists Rem1
          |        (
          |          y =
          |          2.4 + 0 * e0 + 0.05 * e1 + (-3.704) * s + (-0.0480) * (s * e1) + (-7.48605) * s^2 +
          |          (-1.1580) * (s * e0) +
          |          (-0.33796) * (s^2 * e1) +
          |          (-0.05400) * (s * e0^2) +
          |          10.850 * s^3 +
          |          0.46965 * (s^2 * e0) +
          |          (-0.02100) * (s * e0 * e1) +
          |          0.000 * (s * e1^2) +
          |          Rem1 &
          |          s * ((-3991) * 10^(-6)) + 0.00 <= Rem1 & Rem1 <= s * (1096 * 10^(-5)) + 0.00
          |        )
          |    )""".stripMargin.asFormula
    }
  }
}
