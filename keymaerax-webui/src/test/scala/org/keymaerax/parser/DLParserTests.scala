/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.parser

import org.keymaerax.core._
import org.keymaerax.parser.ParseExceptionMatchers.pointAt
import org.keymaerax.{Configuration, FileConfiguration}
import org.scalamock.scalatest.MockFactory
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers
import org.scalatest.{BeforeAndAfterAll, BeforeAndAfterEach}

import scala.collection.mutable.ListBuffer

/**
 * Tests the DL parser.
 * @author
 *   James Gallicchio
 */
class DLParserTests extends AnyFlatSpec with Matchers with BeforeAndAfterEach with BeforeAndAfterAll with MockFactory {
  var parser = new DLParser

  override def beforeAll(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)
  }

  override def beforeEach(): Unit = { parser = new DLParser }

  "DLParser" should "parse multiple invariants" in {
    val annotations = ListBuffer.empty[(Program, Formula)]
    parser.setAnnotationListener((prg, fml) => annotations.append(prg -> fml))
    parser.programParser(
      """{{x'=v, v'=-g+r*v^2, t'=1 & t<=T & x>=0 & v<0}@invariant(
        |  (v'=-g+a*v^2 -> v-g*(T-t)>-(g/p)^(1/2)),
        |  (v'=-g+p*v^2 -> v>=old(v)-g*t))
        |}""".stripMargin
    )
    annotations.length shouldBe 2
  }

  it should "parse parenthesized" in {
    parser("(x+1)") shouldBe parser("x+1")
    parser("(x>=0)") shouldBe parser("x>=0")
  }

  it should "parse formula constants" in { parser("x & y") shouldBe parser("x() & y()") }

  it should "not parse number prime" in {
    the[ParseException] thrownBy parser.termParser("4'") should have message
      """1:2 Error parsing fullTerm at 1:1
        |Found:    "'" at 1:2
        |Expected: ([0-9] | "." | "^" | "*" | "/" | "+" | "-" | end-of-input)
        |Hint: Try ([0-9] | "." | "^" | "*" | "/" | "+" | "-" | end-of-input)""".stripMargin
  }

  it should "parse exponentials" in {
    parser("-2^4") shouldBe Neg(Power(Number(2), Number(4)))
    parser("(-2)^4") shouldBe Power(Number(-2), Number(4))
    parser("(- 2)^4") shouldBe Power(Neg(Number(2)), Number(4))
  }

  it should "parse numbers" in {
    parser("-1") shouldBe (if (Parser.numNeg) Number(-1) else Neg(Number(1)))
    parser("(-1)") shouldBe Number(-1)
    parser("(- 1)") shouldBe Neg(Number(1))
    parser("(-1)*10") shouldBe Times(Number(-1), Number(10))
    parser("-1*10") shouldBe (if (Parser.numNeg) Times(Number(-1), Number(10)) else Neg(Times(Number(1), Number(10))))
    parser("-1*x") shouldBe
      (if (Parser.numNeg) Times(Number(-1), Variable("x")) else Neg(Times(Number(1), Variable("x"))))
  }

  it should "parse sums" in {
    parser("-2-3") shouldBe (if (Parser.numNeg) Minus(Number(-2), Number(3)) else Minus(Neg(Number(2)), Number(3)))
  }

  it should "parse divisions with negations correctly" in {
    parser("2/-3*4") shouldBe
      (if (Parser.numNeg) Times(Divide(Number(2), Number(-3)), Number(4))
       else Times(Divide(Number(2), Neg(Number(3))), Number(4)))
    parser("2/-x*y") shouldBe Times(Divide(Number(2), Neg(Variable("x"))), Variable("y"))
  }

  it should "parse exponentials correctly" in {
    parser("x^-y^z") shouldBe Power(Variable("x"), Neg(Power(Variable("y"), Variable("z"))))
  }

  it should "parse negations correctly" in {
    parser("x*-y*z") shouldBe Times(Variable("x"), Neg(Times(Variable("y"), Variable("z"))))
    parser("2*(3*(-0.1*x))") shouldBe Times(Number(2), Times(Number(3), Neg(Times(Number(0.1), Variable("x")))))
  }

  it should "parse parenthesized formulas with decimal numbers" in {
    parser("!(0.8<=x)") shouldBe Not(LessEqual(Number(0.8), Variable("x")))
  }

  it should "not weak-negate parenthesized negations" in {
    if (Parser.weakNeg) {
      parser("-x*y") shouldBe Neg(Times(Variable("x"), Variable("y")))
      parser("(-x)*y") shouldBe Times(Neg(Variable("x")), Variable("y"))
      // nested once
      parser("x*-y*z") shouldBe Times(Variable("x"), Neg(Times(Variable("y"), Variable("z"))))
      parser("x*(-y)*z") shouldBe Times(Times(Variable("x"), Neg(Variable("y"))), Variable("z"))
      // nested
      parser("x*-y*-z*2") shouldBe Times(Variable("x"), Neg(Times(Variable("y"), Neg(Times(Variable("z"), Number(2))))))
      parser("x*(-y)*(-z)*2") shouldBe
        Times(Times(Times(Variable("x"), Neg(Variable("y"))), Neg(Variable("z"))), Number(2))
      parser("x*(-y)*-z*2") shouldBe
        Times(Times(Variable("x"), Neg(Variable("y"))), Neg(Times(Variable("z"), Number(2))))
      parser("x*-y*(-z)*2") shouldBe
        Times(Variable("x"), Neg(Times(Times(Variable("y"), Neg(Variable("z"))), Number(2))))
    } else {
      parser("-x*y") shouldBe parser("(-x)*y")
      parser("-x*y*z") shouldBe parser("(-x)*y")
      parser("(-(x*y))*z") shouldBe Times(Neg(Times(Variable("x"), Variable("y"))), Variable("z"))
      parser("x*(-y)*z") shouldBe parser("x*-y*z")
      parser("x*(-y)*z") shouldBe Times(Variable("x"), Times(Neg(Variable("y")), Variable("z")))
    }
  }

  it should "parse number differentials" in {
    parser("(4)'") shouldBe Differential(Number(4))
    parser("(0)'") shouldBe Differential(Number(0))
    parser("(0)'+0") shouldBe Plus(Differential(Number(0)), Number(0))
    parser("[x:=(4)';]x>=(4)'") shouldBe
      Box(Assign(Variable("x"), Differential(Number(4))), GreaterEqual(Variable("x"), Differential(Number(4))))
  }

  it should "parse differential symbols" in {
    parser.termParser("x_'") shouldBe DifferentialSymbol(Variable("x_"))
    parser("x_'") shouldBe parser.termParser("x_'")
  }

  it should "parse predicationals" in {
    parser.formulaParser("P{z'=1}") shouldBe
      PredicationalOf(Function("P", None, Bool, Bool), Equal(DifferentialSymbol(Variable("z")), Number(1)))
    parser("P{z'=1}") shouldBe parser.formulaParser("P{z'=1}")
  }

  it should "not parse p->q<-r" in {
    the[ParseException] thrownBy parser("p()->q()<-r()") should pointAt(1, 9)
    the[ParseException] thrownBy parser("(p()->q())<-r()") should pointAt(1, 11)

    parser("(p()->q()) <- r()") shouldBe Imply(
      PredOf(Function("r", None, Unit, Bool), Nothing),
      Imply(PredOf(Function("p", None, Unit, Bool), Nothing), PredOf(Function("q", None, Unit, Bool), Nothing)),
    )
  }

  it should "parse reverse implication of base terms" in {
    val x = FuncOf(Function("x", None, Unit, Real), Nothing)
    val y = Variable("y")
    parser("y>x() <- x()<y") shouldBe Imply(Less(x, y), Greater(y, x))
  }

  it should "parse when function name and arguments are separated by whitespace " in {
    // @note DLParser does not know interpreted symbols unless explicit interpretation is listed
    parser("min (x,y)") shouldBe
      FuncOf(Function("min", None, Tuple(Real, Real), Real), Pair(Variable("x"), Variable("y")))
    parser("min\n(x,y)") shouldBe
      FuncOf(Function("min", None, Tuple(Real, Real), Real), Pair(Variable("x"), Variable("y")))
  }

  it should "not parse x//y" in {
    the[ParseException] thrownBy parser("x//y") should have message
      """1:3 Error parsing term at 1:1
        |Found:    "/y" at 1:3
        |Expected: (number | dot | function | unitFunctional | variable | termList | "__________" | "-")
        |Hint: Try ("(" | [0-9] | "." | "•" | [a-zA-Z] | "__________" | "-")""".stripMargin
  }

  it should "parse dual game symbol notation" in { parser("game;^@;") shouldBe Dual(ProgramConst("game")) }

  it should "parse simple dual game symbol notation" in { parser("game^@;") shouldBe Dual(ProgramConst("game")) }

}
