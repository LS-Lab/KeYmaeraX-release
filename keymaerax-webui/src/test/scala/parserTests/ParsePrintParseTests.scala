package parserTests

/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import org.scalatest.{FlatSpec, Matchers}
import test._

/**
 * Created by smitsch on 1/8/15.
 * @author Stefan Mitsch
 */
class ParsePrintParseTests extends FlatSpec with Matchers {

    val randomTrials = 40*10
    val randomComplexity = 20
    val rand = new RandomFormula()

  // type declaration header for tests
  def makeInput(program : String) : String = {
    "Functions. B a. B b. B c. End." +
    "ProgramVariables. R p. R q. R r. R s. R r_0. End." +
    "Problem." + program + "\nEnd."
  }

  "Parsing of pretty-printed ODEs" should "be the same as the original parse result" in {
    val exprs =
      "[{x'=y}]x>0" ::
      "[{x'=y & x>0}]x>0" ::
      "[{x'=y, y'=z & x>0}]x>0" ::
      "[{x'=y, y'=z, z'=3 & z>1 & z>2}]x>0" :: Nil

    for (e <- exprs) {
      val expected = KeYmaeraXParser(e)
      KeYmaeraXParser(KeYmaeraXPrettyPrinter(expected)) shouldBe expected
    }
  }

  it should "parse, print, and parse ODEs in sequential compositions" in {
    val exprs =
      "[{x'=y}; x:=2;]x>0" ::
//      "[x:=2; {x'=y}]x>0" :: // TODO not yet supported by parser
      "[{x'=y}*]x>0" ::
      "[{{x'=y}; x:=2;}*]x>0" ::
//      "[{x:=2; {x'=y}}*]x>0" :: // TODO not yet supported by parser
        Nil

    for (e <- exprs) {
      val expected = KeYmaeraXParser(e)
      KeYmaeraXParser(KeYmaeraXPrettyPrinter(expected)) shouldBe expected
    }
  }

  it should "print and parse nested choices consistently" in {
    val exprs =
      "[x:=1; ++ x:=2; ++ x:=3;]x>0" ::
      "[x:=10;x:=11; ++ x:=20;x:=21; ++ x:=30;x:=31;]x>0" ::
      "[{x:=10;x:=11; ++ x:=20;x:=21; ++ x:=30;x:=31;};x:=40;]x>0" ::
      "[x:=0;{x:=10;x:=11; ++ x:=20;x:=21; ++ x:=30;x:=31;};x:=40;]x>0" ::
      "[{x:=1; ++ x:=2;}++x:=3;]x>0" :: Nil

    for (e <- exprs) {
      val expected = KeYmaeraXParser(e)
      KeYmaeraXParser(KeYmaeraXPrettyPrinter(expected)) shouldBe expected
    }
  }

  it should "print and parse sequences with superfluous parentheses" in {
    val exprs =
      "[{x:=1;x:=2;};x:=3;]x>0" ::
      "[{{x:=1;x:=2;};x:=3;} {{x:=4;};x:=5;}]x>0" :: Nil

    for (e <- exprs) {
      val expected = KeYmaeraXParser(e)
      KeYmaeraXParser(KeYmaeraXPrettyPrinter(expected)) shouldBe expected
    }
  }

  "Parsing pretty-printer output" should "be the same as the original expression (random)" in {
    for (i <- 1 to randomTrials) {
		val expected = rand.nextFormula(randomComplexity)
      // asFormula runs the parser, but declares the variables occurring in the formula
      KeYmaeraXPrettyPrinter(expected).asFormula shouldBe expected
    }
  }
}
