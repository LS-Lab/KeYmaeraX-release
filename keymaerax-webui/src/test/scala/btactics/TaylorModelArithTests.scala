package btactics

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

  import PolynomialArithV2Helpers._

  val context3 = ("-1 <= x0(), x0() <= 1, -1 <= y0(), y0() <= 1, -1 <= z0(), z0() <= 1," +
    "x = x0() + y0() + rx, -0.01 <= rx, rx <= 0.02," +
    "y = 0.5*x0() - y0() + ry, 0 <= ry, ry <= 0.1").split(',').map(_.asFormula).toIndexedSeq
  lazy val ta3 = new TaylorModelArith(context3, "x0(),y0(),z0(),rx,ry".split(',').map(_.asTerm).toIndexedSeq, 5, 4)
  lazy val x0 = ta3.polynomialRing.ofTerm("x0()".asTerm)
  lazy val y0 = ta3.polynomialRing.ofTerm("y0()".asTerm)
  lazy val tm1 = ta3.TM("x".asTerm, x0 + y0, "-0.01".asTerm, "0.02".asTerm, QE)
  lazy val tm2 = ta3.TM("y".asTerm, ta3.polynomialRing.Const(BigDecimal("0.5")) * x0 - y0, "0".asTerm, "0.1".asTerm, QE)
  lazy val tm3 = ta3.Exact(ta3.polynomialRing.ofTerm("1/3".asTerm)) *! tm1

  "Taylor models" should "add exactly" in withMathematica { qeTool =>
    (tm1 +! tm2).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x+y=1.5*x0()+err_&-0.01<=err_&err_<=0.12)".asFormula
  }

  it should "subtract exactly" in withMathematica { qeTool =>
    (tm1 -! tm2).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x-y=0.5*x0()+2*y0()+err_&-0.11<=err_&err_<=0.02)".asFormula
  }

  it should "multiply exactly" in withMathematica { qeTool =>
    (tm1 *! tm2).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x*y=0.5*x0()^2+- 0.5*x0()*y0()+- 1*y0()^2+err_&-0.231<=err_&err_<=0.232)".asFormula
  }

  it should "negate" in withMathematica { qeTool =>
    (-tm1).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (-x=-x0()+- 1*y0()+err_&-0.02<=err_&err_<=0.01)".asFormula
  }

  it should "square exactly" in withMathematica { qeTool =>
    tm1.squareExact.prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x^2=x0()^2+2*x0()*y0()+1*y0()^2+err_&-0.08<=err_&err_<=0.0804)".asFormula
  }

  it should "^1" in withMathematica { qeTool =>
    (tm1^1).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x^1=x0()+1*y0()+err_&-0.01<=err_&err_<=0.02)".asFormula
  }

  it should "^(2*n)" in withMathematica { qeTool =>
    (tm1^4).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x^4=x0()^4+4*x0()^3*y0()+6*x0()^2*y0()^2+4*x0()*y0()^3+1*y0()^4+err_&-0.64<=err_&err_<=0.64967)".asFormula
  }
  it should "^(2*n + 1)" in withMathematica { qeTool =>
    (tm1^3).prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ (x^3=x0()^3+3*x0()^2*y0()+3*x0()*y0()^2+1*y0()^3+err_&-0.2024<=err_&err_<=0.24241)".asFormula
  }

  it should "exact" in withMathematica { qeTool =>
    import ta3._
    import ta3.polynomialRing._
    val a = ofTerm("x0()".asTerm)
    val b = ofTerm("1".asTerm)
    val c = ofTerm("1/3".asTerm)
    val tmA = Exact(a)
    val tmB = Exact(b)
    val tmC = Exact(c)
    (tmA).prettyPrv.conclusion.succ(0) shouldBe "\\exists err_ (x0()=x0()+err_&0<=err_&err_<=0)".asFormula
    (tmB).prettyPrv.conclusion.succ(0) shouldBe "\\exists err_ (1=1+err_&0<=err_&err_<=0)".asFormula
    (tmC).prettyPrv.conclusion.succ(0) shouldBe "\\exists err_ (1/3=1/3+err_&0<=err_&err_<=0)".asFormula
  }

  it should "approx" in withMathematica { qeTool =>
    import ta3._
    import polynomialRing._
    val tm = (tm3 +! tm2).squareExact
    val tmA = tm.approx(5)
    tmA.prettyPrv.conclusion.succ(0) shouldBe
      "\\exists err_ ((1/3*x+y)^2=0.6944*x0()^2+- 1.112*x0()*y0()+0.4444*y0()^2+err_&-0.32102<=err_&err_<=0.33240)".asFormula
  }

  it should "form Horner" in withMathematica { qeTool =>
    import ta3._
    import ta3.polynomialRing._
    val hornerPrv = toHorner(ofTerm("(x0()+y0()+z0())^2".asTerm))
    hornerPrv shouldBe 'proved
    hornerPrv.conclusion.ante shouldBe 'empty
    hornerPrv.conclusion.succ.loneElement shouldBe
      "(x0()+y0()+z0())^2=z0()*z0()+y0()*(z0()*2+y0())+x0()*(z0()*2+y0()*2+x0())".asFormula
  }

}
