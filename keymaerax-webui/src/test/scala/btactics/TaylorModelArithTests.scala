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

  val context3 = ("-1 <= x0(), x0() <= 1, -1 <= y0(), y0() <= 1, -1 <= z0(), z0() <= 1," +
    "x = x0() + y0() + rx, -0.01 <= rx, rx <= 0.02," +
    "y = 0.5*x0() - y0() + ry, 0 <= ry, ry <= 0.1").split(',').map(_.asFormula).toIndexedSeq
  lazy val ta3 = new TaylorModelArith(context3, "x0(),y0(),z0(),rx,ry".split(',').map(_.asTerm).toIndexedSeq, 10, 4)

  "Taylor models" should "add exactly" in withMathematica { qeTool =>
    import ta3._
    import ta3.polynomialRing._
    val x0 = ofTerm("x0()".asTerm)
    val y0 = ofTerm("y0()".asTerm)
    val tm1 = TM("x".asTerm, x0 + y0, "-0.01".asTerm, "0.02".asTerm, QE)
    val tm2 = TM("y".asTerm, Const(BigDecimal("0.5")) * x0 - y0, "0".asTerm, "0.1".asTerm, QE)
    println(tm1)
    println(tm2)
    println(tm1 +! tm2)
  }

  it should "subtract exactly" in withMathematica { qeTool =>
    import ta3._
    import ta3.polynomialRing._
    val x0 = ofTerm("x0()".asTerm)
    val y0 = ofTerm("y0()".asTerm)
    val tm1 = TM("x".asTerm, x0 + y0, "-0.01".asTerm, "0.02".asTerm, QE)
    val tm2 = TM("y".asTerm, Const(BigDecimal("0.5")) * x0 - y0, "0".asTerm, "0.1".asTerm, QE)
    println(tm1)
    println(tm2)
    println(tm1 -! tm2)
  }

  it should "multiply exactly" in withMathematica { qeTool =>
    import ta3._
    import ta3.polynomialRing._
    val x0 = ofTerm("x0()".asTerm)
    val y0 = ofTerm("y0()".asTerm)
    val tm1 = TM("x".asTerm, x0 + y0, "-0.01".asTerm, "0.02".asTerm, QE)
    val tm2 = TM("y".asTerm, Const(BigDecimal("0.5")) * x0 - y0, "0".asTerm, "0.1".asTerm, QE)
    println(tm1)
    println(tm2)
    println(tm1 *! tm2)
  }

  it should "negate" in withMathematica { qeTool =>
    import ta3._
    import ta3.polynomialRing._
    val x0 = ofTerm("x0()".asTerm)
    val y0 = ofTerm("y0()".asTerm)
    val tm1 = TM("x".asTerm, x0 + y0, "-0.01".asTerm, "0.02".asTerm, QE)
    println(tm1)
    println(-tm1)
  }

  it should "square exactly" in withMathematica { qeTool =>
    import ta3._
    import ta3.polynomialRing._
    val x0 = ofTerm("x0()".asTerm)
    val y0 = ofTerm("y0()".asTerm)
    val tm1 = TM("x".asTerm, x0 + y0, "-0.01".asTerm, "0.02".asTerm, QE)
    println(tm1)
    println(tm1.squareExact)
  }

  it should "^1" in withMathematica { qeTool =>
    import ta3._
    import ta3.polynomialRing._
    val x0 = ofTerm("x0()".asTerm)
    val y0 = ofTerm("y0()".asTerm)
    val tm1 = TM("x".asTerm, x0 + y0, "-0.01".asTerm, "0.02".asTerm, QE)
    println(tm1)
    println(tm1^!1)
  }

  it should "^(2*n)" in withMathematica { qeTool =>
    import ta3._
    import ta3.polynomialRing._
    val x0 = ofTerm("x0()".asTerm)
    val y0 = ofTerm("y0()".asTerm)
    val tm1 = TM("x".asTerm, x0 + y0, "-0.01".asTerm, "0.02".asTerm, QE)
    println(tm1)
    println(tm1^!4)
  }
  it should "^(2*n + 1)" in withMathematica { qeTool =>
    import ta3._
    import ta3.polynomialRing._
    val x0 = ofTerm("x0()".asTerm)
    val y0 = ofTerm("y0()".asTerm)
    val tm1 = TM("x".asTerm, x0 + y0, "-0.01".asTerm, "0.02".asTerm, QE)
    println(tm1)
    println(tm1^!3)
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
    println(tmA)
    println(tmB)
    println(tmC)
  }

  it should "approx" in withMathematica { qeTool =>
    import ta3._
    import ta3.polynomialRing._
    import PolynomialArithV2Helpers._
    val x0 = ofTerm("x0()".asTerm)
    val y0 = ofTerm("y0()".asTerm)
    val tm1 = Exact(ofTerm("1/3".asTerm)) *! TM("x".asTerm, x0 + y0, "-0.01".asTerm, "0.02".asTerm, QE)
    val tm2 = TM("y".asTerm, Const(BigDecimal("0.5")) * x0 - y0, "0".asTerm, "0.1".asTerm, QE)
    val tm = (tm1 +! tm2)^!2
    val tmA = tm.approx(5)
    tmA.elem shouldBe "(1/3*x+y)^2".asTerm
    rhsOf(tmA.poly.prettyRepresentation) shouldBe "0.6944*x0()^2+- 1.112*x0()*y0()+0.4444*y0()^2".asTerm
    tmA.lower shouldBe "-32099*10^-5".asTerm
    tmA.upper shouldBe "33236*10^-5".asTerm
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
