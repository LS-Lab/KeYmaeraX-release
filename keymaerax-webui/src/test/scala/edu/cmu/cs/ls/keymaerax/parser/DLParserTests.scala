/**
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import org.scalamock.scalatest.MockFactory
import org.scalatest.{BeforeAndAfterAll, BeforeAndAfterEach, FlatSpec, Matchers}

import scala.collection.mutable.ListBuffer

/**
 * Tests the DL parser.
 * @author James Gallicchio
 */
class DLParserTests extends FlatSpec with Matchers with BeforeAndAfterEach with BeforeAndAfterAll with MockFactory {

  override def beforeAll(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)
  }

  override def afterEach(): Unit = {
    DLParser.setAnnotationListener((_, _) => {})
  }

  "DLParser" should "parse multiple invariants" in {
    val annotations = ListBuffer.empty[(Program, Formula)]
    DLParser.setAnnotationListener((prg, fml) => annotations.append(prg -> fml))
    DLParser.programParser(
      """{{x'=v, v'=-g+r*v^2, t'=1 & t<=T & x>=0 & v<0}@invariant(
        |  (v'=-g+a*v^2 -> v-g*(T-t)>-(g/p)^(1/2)),
        |  (v'=-g+p*v^2 -> v>=old(v)-g*t))
        |}""".stripMargin
    )
    annotations.length shouldBe 2
  }

  it should "parse parenthesized" in {
    DLParser("(x+1)") shouldBe DLParser("x+1")
    DLParser("(x>=0)") shouldBe DLParser("x>=0")
  }

  it should "parse formula constants" in {
    DLParser("x & y") shouldBe DLParser("x() & y()")
  }

  it should "not parse number prime" in {
    the [ParseException] thrownBy DLParser.termParser("4'") should have message
      """1:2 Error parsing fullTerm at 1:1
        |Found:    "'" at 1:2
        |Expected: ([0-9] | "." | "^" | "*" | "/" | "+" | "-" | end-of-input)
        |Hint: Try ([0-9] | "." | "^" | "*" | "/" | "+" | "-" | end-of-input)""".stripMargin
  }

  it should "parse exponentials" in {
    DLParser("-2^4") shouldBe Neg(Power(Number(2), Number(4)))
    DLParser("(-2)^4") shouldBe Power(Number(-2), Number(4))
    DLParser("(- 2)^4") shouldBe Power(Neg(Number(2)), Number(4))
  }

  it should "parse numbers" in {
    DLParser("-1") shouldBe (if (Parser.numNeg) Number(-1) else Neg(Number(1)))
    DLParser("(-1)") shouldBe Number(-1)
    DLParser("(- 1)") shouldBe Neg(Number(1))
    DLParser("(-1)*10") shouldBe Times(Number(-1), Number(10))
    DLParser("-1*10") shouldBe (if (Parser.numNeg) Times(Number(-1), Number(10)) else Neg(Times(Number(1), Number(10))))
    DLParser("-1*x") shouldBe (if (Parser.numNeg) Times(Number(-1), Variable("x")) else Neg(Times(Number(1), Variable("x"))))
  }

  it should "parse sums" in {
    DLParser("-2-3") shouldBe (if (Parser.numNeg) Minus(Number(-2), Number(3)) else Minus(Neg(Number(2)), Number(3)))
  }

  it should "parse divisions with negations correctly" in {
    DLParser("2/-3*4") shouldBe (if (Parser.numNeg) Times(Divide(Number(2), Number(-3)), Number(4)) else Times(Divide(Number(2), Neg(Number(3))), Number(4)))
    DLParser("2/-x*y") shouldBe Times(Divide(Number(2), Neg(Variable("x"))), Variable("y"))
  }

  it should "parse exponentials correctly" in {
    DLParser("x^-y^z") shouldBe Power(Variable("x"), Neg(Power(Variable("y"), Variable("z"))))
  }

  it should "parse negations correctly" in {
    DLParser("x*-y*z") shouldBe Times(Variable("x"), Neg(Times(Variable("y"), Variable("z"))))
  }

  it should "parse parenthesized formulas with decimal numbers" in {
    DLParser("!(0.8<=x)") shouldBe Not(LessEqual(Number(0.8), Variable("x")))
  }

  it should "parse number differentials" in {
    DLParser("(4)'") shouldBe Differential(Number(4))
    DLParser("(0)'") shouldBe Differential(Number(0))
    DLParser("(0)'+0") shouldBe Plus(Differential(Number(0)), Number(0))
    DLParser("[x:=(4)';]x>=(4)'") shouldBe Box(Assign(Variable("x"), Differential(Number(4))), GreaterEqual(Variable("x"), Differential(Number(4))))
  }

  it should "parse differential symbols" in {
    DLParser.termParser("x_'") shouldBe DifferentialSymbol(Variable("x_"))
    DLParser("x_'") shouldBe DLParser.termParser("x_'")
  }

  it should "parse predicationals" in {
    DLParser.formulaParser("P{z'=1}") shouldBe PredicationalOf(Function("P", None, Bool, Bool), Equal(DifferentialSymbol(Variable("z")), Number(1)))
    DLParser("P{z'=1}") shouldBe DLParser.formulaParser("P{z'=1}")
  }

  it should "not parse p->q<-r" in {
    the [ParseException] thrownBy DLParser("p()->q()<-r()") should have message
      """1:9 Error parsing fullExpression at 1:1
        |Found:    "<-r()" at 1:9
        |Expected: ("'" | "^" | "*" | "/" | "+" | "-" | comparator | "&" | "∧" | "|" | "∨" | "->" | "→" | " <- " | "←" | "<->" | "↔" | end-of-input)
        |Hint: Try ("'" | "^" | "*" | "/" | "+" | "-" | "=" | "!=" | "≠" | ">=" | "≥" | ">" | "<=" | "≤" | "&" | "∧" | "|" | "∨" | "->" | "→" | [ \t\r\n] | " <- " | "←" | "<->" | "↔" | end-of-input)""".stripMargin
    //@note disallowed even though unambiguous because can't tell whether a formula was parenthesized once it's parsed
    the [ParseException] thrownBy DLParser("(p()->q())<-r()") should have message
      """1:11 Error parsing fullExpression at 1:1
        |Found:    "<-r()" at 1:11
        |Expected: ("'" | "&" | "∧" | "|" | "∨" | "->" | "→" | " <- " | "←" | "<->" | "↔" | end-of-input)
        |Hint: Try ("'" | "&" | "∧" | "|" | "∨" | "->" | "→" | [ \t\r\n] | " <- " | "←" | "<->" | "↔" | end-of-input)""".stripMargin

    DLParser("(p()->q()) <- r()") shouldBe Imply(PredOf(Function("r", None, Unit, Bool), Nothing),
      Imply(PredOf(Function("p", None, Unit, Bool), Nothing), PredOf(Function("q", None, Unit, Bool), Nothing)))
  }

  it should "parse reverse implication of base terms" in {
    val x = FuncOf(Function("x", None, Unit, Real), Nothing)
    val y = Variable("y")
    DLParser("y>x() <- x()<y") shouldBe Imply(Less(x, y), Greater(y, x))
  }

  it should "not parse x//y" in {
    the [ParseException] thrownBy DLParser("x//y") should have message
      """1:3 Error parsing term at 1:1
        |Found:    "/y" at 1:3
        |Expected: ("(" | number | dot | function | unitFunctional | variable | termList | "__________" | "-")
        |Hint: Try ("(" | [0-9] | "." | "•" | [a-zA-Z] | "__________" | "-")""".stripMargin
  }

}