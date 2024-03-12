/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import edu.cmu.cs.ls.keymaerax.bellerophon.LazySequentialInterpreter
import edu.cmu.cs.ls.keymaerax.btactics.RandomFormula
import edu.cmu.cs.ls.keymaerax.core.{PrettyPrinter => CorePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool

import org.scalatest.{BeforeAndAfterAll, BeforeAndAfterEach, FlatSpec, Matchers}
import org.scalatest.prop.TableDrivenPropertyChecks._

import scala.collection.immutable.Map

/**
 * Created by smitsch on 1/8/15.
 * @author
 *   Stefan Mitsch
 */
class ParsePrintParseTests extends FlatSpec with Matchers with BeforeAndAfterEach with BeforeAndAfterAll {
  private val randomTrials = 20
  private val randomComplexity = 25
  private val rand = new RandomFormula()

  override def beforeAll(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    KeYmaeraXTool.init(Map(
      KeYmaeraXTool.INIT_DERIVATION_INFO_REGISTRY -> "false",
      KeYmaeraXTool.INTERPRETER -> LazySequentialInterpreter.getClass.getSimpleName,
    ))
  }

  override protected def beforeEach(): Unit = CorePrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter)

  "Parsing of pretty-printed ODEs" should "be the same as the original parse result" in {
    val exprs = Table(
      "[{x'=y}]x>0",
      "[{x'=y & x>0}]x>0",
      "[{x'=y, y'=z & x>0}]x>0",
      "[{x'=y, y'=z & x>0}]x>0",
      "[{x'=y, y'=z, z'=3 & z>1 & z>2}]x>0",
    )

    forEvery(exprs) { e =>
      val expected = Parser(e)
      Parser(CorePrettyPrinter(expected)) shouldBe expected
    }
  }

  it should "parse, print, and parse ODEs in sequential compositions" in {
    val exprs = Table(
      "[{x'=y}; x:=2;]x>0",
      "[x:=2; {x'=y}]x>0",
      "[{{x'=y}}*]x>0",
      "[{{x'=y}; x:=2;}*]x>0",
      "[{x:=2; {x'=y}}*]x>0",
    )

    forEvery(exprs) { e =>
      val expected = Parser(e)
      Parser(CorePrettyPrinter(expected)) shouldBe expected
    }
  }

  it should "print and parse nested choices consistently" in {
    val exprs = Table(
      "[x:=1; ++ x:=2; ++ x:=3;]x>0",
      "[x:=10;x:=11; ++ x:=20;x:=21; ++ x:=30;x:=31;]x>0",
      "[{x:=10;x:=11; ++ x:=20;x:=21; ++ x:=30;x:=31;};x:=40;]x>0",
      "[x:=0;{x:=10;x:=11; ++ x:=20;x:=21; ++ x:=30;x:=31;};x:=40;]x>0",
      "[{x:=1; ++ x:=2;}++x:=3;]x>0",
    )

    forEvery(exprs) { e =>
      val expected = Parser(e)
      Parser(CorePrettyPrinter(expected)) shouldBe expected
    }
  }

  it should "print and parse sequences with superfluous parentheses" in {
    val exprs = Table("[{x:=1;x:=2;};x:=3;]x>0", "[{{x:=1;x:=2;};x:=3;} {{x:=4;};x:=5;}]x>0")

    forEvery(exprs) { e =>
      val expected = Parser(e)
      Parser(CorePrettyPrinter(expected)) shouldBe expected
    }
  }

  it should "not print and parse a formula with if then else as variable names." ignore {
    val exprs = Table("if = then", "then = else", "if = else", "else = then", "then = if")

    forEvery(exprs) { e => a[ParseException] should be thrownBy Parser(e) }
  }

  it should "print and parse if-then-else" in {
    val exprs = Table(
      "if(x < 0)  { x := -x; x := x;} else {?true;}",
      "if (x < 0) { x := -x;} else {?true;}",
      "if (x < 0) { x := -x;} else {x := x * 2;}",
      "if (acc <= 0) { acc := 0;} else {if (SB < A) {acc := SB;} else {acc := A;}}",
      "<{if (x = 0) {x := 1; y := 0;} else {y := 3; a := a + 5; ?(x = x);}}>x != y",
      "<if (x = 0) {x := 1; y := 0;} else {y := 3;} a := a + 5; ?(x = x);>x != y",
      "x = 0 -> [if (x = 0){ x := 1; y := 0; }else {y := 3;} a := a + 5; ?(x = x);]x > y",
    )

    forEvery(exprs) { e =>
      val expected = Parser(e)
      Parser(CorePrettyPrinter(expected)) shouldBe expected
    }
  }

  it should "print and parse small decimals without scientific notation" in {
    val expr = "0.00000001"
    val expected = Parser(expr)
    val printed = CorePrettyPrinter(expected)
    val reparsed = Parser(printed)
    reparsed shouldBe expected
  }

  "Parsing pretty-printer output" should "be the same as the original expression (random)" in {
    for (_ <- 1 to randomTrials) {
      val expected = rand.nextFormulaEpisode().nextFormula(randomComplexity)
      // asFormula runs the parser, but declares the variables occurring in the formula
      CorePrettyPrinter(expected).asFormula shouldBe expected
    }
  }

  "Prettier printer" should "print spaces to disambiguate negation from negative number" in {
    new KeYmaeraXPrettierPrinter(50)("-(1*10)<=20".asFormula) shouldBe
      (if (Parser.numNeg) "-(1 * 10) <= 20" else "-1 * 10 <= 20")
    new KeYmaeraXPrettierPrinter(50)("(-1)*10<=20".asFormula) shouldBe
      (if (Parser.numNeg) "-1 * 10 <= 20" else "(-1) * 10 <= 20")
    new KeYmaeraXPrettierPrinter(50)("-x<=20".asFormula) shouldBe "-x <= 20"
  }
}
