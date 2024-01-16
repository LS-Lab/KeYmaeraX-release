/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.InterpretedSymbols
import edu.cmu.cs.ls.keymaerax.tools.ext.Mathematica
import edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool
import org.scalatest.LoneElement._

/** Tests for trustworthy BigDecimal computations
  * @author Fabian Immler
  */
class BigDecimalQEToolTests extends TacticTestBase  {

  val numbers =
    ("-2,-1,0,1,2,3,10,730963476657,1180918287134404971234765536279227090481580443894," +
    "-0.2,0.3,0.000000000000000000000000000000000000000000000000000000000000000000001," +
    "0.730967787376657," +
    "16543749471661998771.6510510573789608," +
    "-51890712899135751252332814755814641.118091828713440497765536090481580443894," +
    "629649.30412662647769980700759557641946737912396204471525278051877116806").split(',').map(i => Number(BigDecimal(i)))

  def checkEval(mathematica: Mathematica, t: Term, mayFail: Boolean) = {
    try {
      val u = Number(BigDecimalQETool.eval(t))
      val fml = Equal(t, u)
      val res = mathematica.qe(fml).fact
      res shouldBe Symbol("proved")
      res.conclusion.ante shouldBe Symbol("empty")
      res.conclusion.succ.loneElement shouldBe Equiv(fml, True)
    } catch {
      case iae: IllegalArgumentException =>
        if (!mayFail) throw iae
    }
  }

  "unary operations" should "agree with QE" in withMathematica { mathematica =>
    for ( n <- numbers ) {
      checkEval(mathematica, Neg(n), false)
      checkEval(mathematica, Differential(n), true)
      withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
        checkEval(mathematica, FuncOf(InterpretedSymbols.absF, n), false)
      }
      checkEval(mathematica, FuncOf(Function("f", None, Real, Real), n), true)
    }
  }

  "binary operations" should "agree with QE" in withMathematica { mathematica =>
    for ( n <- numbers ; m <- numbers) {
      checkEval(mathematica, Plus(n, m), false)
      checkEval(mathematica, Minus(n, m), false)
      checkEval(mathematica, Times(n, m), false)
      checkEval(mathematica, Divide(n, m), true)
      checkEval(mathematica, Power(n, m), true)
      withTemporaryConfig(Map(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS -> "true")) {
        checkEval(mathematica, FuncOf(InterpretedSymbols.minF, Pair(n, m)), false)
        checkEval(mathematica, FuncOf(InterpretedSymbols.maxF, Pair(n, m)), false)
      }
      checkEval(mathematica, FuncOf(Function("f", None, Tuple(Real, Real), Real), Pair(n, m)), true)
    }
  }

  def checkEval(mathematica: Mathematica, fml: Formula, mayFail: Boolean) = {
    try {
      val b = if (BigDecimalQETool.eval(fml)) True else False
      val res = mathematica.qe(fml).fact
      res shouldBe Symbol("proved")
      res.conclusion.ante shouldBe Symbol("empty")
      res.conclusion.succ.loneElement shouldBe
        Equiv(fml, b)
    } catch {
      case iae: IllegalArgumentException =>
        if (!mayFail) throw iae
    }
  }

  "comparisons" should "agree with QE" in withMathematica { mathematica =>
    for ( n <- numbers ; m <- numbers) {
      checkEval(mathematica, Less(n, m), false)
      checkEval(mathematica, LessEqual(n, m), false)
      checkEval(mathematica, Equal(n, m), false)
      checkEval(mathematica, NotEqual(n, m), false)
      checkEval(mathematica, Greater(n, m), false)
      checkEval(mathematica, GreaterEqual(n, m), false)
    }
  }

  "division" should "return the exact result" in withMathematica { mathematica =>
    checkEval(mathematica, "1/2".asTerm, false)
    checkEval(mathematica, "1/-2".asTerm, false)
    checkEval(mathematica, "3/3".asTerm, false)
    checkEval(mathematica, "-3/3".asTerm, false)
    checkEval(mathematica, "14/7".asTerm, false)
    checkEval(mathematica, "-14/-7".asTerm, false)
    checkEval(mathematica, "1/0.02".asTerm, false)
    checkEval(mathematica, "0.005/0.02".asTerm, false)
  }

  "division" should "fail for nonterminating decimal expansion of exact result" in withMathematica { mathematica =>
    a [IllegalArgumentException] should be thrownBy checkEval(mathematica, "1/3".asTerm, false)
    a [IllegalArgumentException] should be thrownBy checkEval(mathematica, "4/3".asTerm, false)
    a [IllegalArgumentException] should be thrownBy checkEval(mathematica, "15/7".asTerm, false)
    a [IllegalArgumentException] should be thrownBy checkEval(mathematica, "1/0.03".asTerm, false)
    a [IllegalArgumentException] should be thrownBy checkEval(mathematica, "1/0".asTerm, false)
  }

  "boolean combinations" should "agree with QE" in withMathematica { mathematica =>
    for ( b <- True::False::Nil ; c <- True::False::Nil) {
      checkEval(mathematica, And(b, c), false)
      checkEval(mathematica, Or(b, c), false)
      checkEval(mathematica, Imply(b, c), false)
      checkEval(mathematica, Equiv(b, c), false)
    }
    checkEval(mathematica, Not(True), false)
    checkEval(mathematica, Not(False), false)
    checkEval(mathematica, True, false)
    checkEval(mathematica, False, false)

    checkEval(mathematica, Box(Test(True), True), true)
  }

}
