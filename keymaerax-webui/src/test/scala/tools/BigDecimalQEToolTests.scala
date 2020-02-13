package edu.cmu.cs.ls.keymaerax.tools

import java.math.{MathContext, RoundingMode}

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.qe.BigDecimalQETool

/** Tests for trustworthy BigDecimal computations
  * @author Fabian Immler
  */
class BigDecimalQEToolTests extends TacticTestBase  {

  "eval" should "enforce arbitrary precision" in withMathematica { _ =>
    val a = BigDecimal("123", new MathContext(3, RoundingMode.FLOOR))
    val b = BigDecimal("0.12345", new MathContext(5, RoundingMode.FLOOR))
    (a + b) shouldBe BigDecimal("123.12345")
    (b + a) shouldBe BigDecimal("123.12345")
    BigDecimalQETool.eval(Plus(Number(a), Number(b))) shouldBe BigDecimal("123.12345").bigDecimal
    (a * b) shouldBe BigDecimal("15.1")
    (b * a) shouldBe BigDecimal("15.184")
    BigDecimalQETool.eval(Times(Number(a), Number(b))) shouldBe BigDecimal("15.18435").bigDecimal
    BigDecimalQETool.eval(Times(Number(b), Number(a))) shouldBe BigDecimal("15.18435").bigDecimal
  }

  it should "evaluate interpreted functions" in withMathematica { _ =>
    BigDecimalQETool.eval("min(2.7182,3.14159)".asTerm) shouldBe BigDecimal("2.7182").bigDecimal
    BigDecimalQETool.eval("max(2.7182,3.14159)".asTerm) shouldBe BigDecimal("3.14159").bigDecimal
    BigDecimalQETool.eval("abs(-2.7182)".asTerm) shouldBe BigDecimal("2.7182").bigDecimal
  }
}
