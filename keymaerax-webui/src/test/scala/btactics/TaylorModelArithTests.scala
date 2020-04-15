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
  lazy val ta3 = new TaylorModelArith(context3, "x0(),y0(),z0(),rx,ry".split(',').map(_.asTerm).toIndexedSeq, 10, 3)

  "Taylor models" should "add" in withMathematica { qeTool =>
    import ta3._
    import ta3.polynomialRing._
    val x0 = ofTerm("x0()".asTerm)
    val y0 = ofTerm("y0()".asTerm)
    val tm1 = TM("x".asTerm, x0 + y0, "-0.01".asTerm, "0.02".asTerm, QE)
    val tm2 = TM("y".asTerm, Const(BigDecimal("0.5")) * x0 - y0, "0".asTerm, "0.1".asTerm, QE)
    println(tm1)
    println(tm2)
    println(tm1 + tm2)
  }

  it should "multiply" in withMathematica { qeTool =>
    import ta3._
    import ta3.polynomialRing._
    val x0 = ofTerm("x0()".asTerm)
    val y0 = ofTerm("y0()".asTerm)
    val tm1 = TM("x".asTerm, x0 + y0, "-0.01".asTerm, "0.02".asTerm, QE)
    val tm2 = TM("y".asTerm, Const(BigDecimal("0.5")) * x0 - y0, "0".asTerm, "0.1".asTerm, QE)
    println(tm1)
    println(tm2)
    println(tm1 * tm2)
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
