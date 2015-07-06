package edu.cmu.cs.ls.keymaerax.parser

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser._
import org.scalatest.{PrivateMethodTester, Matchers, FlatSpec}

import test.RandomFormula

/**
 * Tests the parser on pretty prints of randomly generated formulas
 * @author aplatzer
 */
class RandomParserTests extends FlatSpec with Matchers {
  val randomTrials = 40000
  val randomComplexity = 6
  val rand = new RandomFormula()


  val pp = KeYmaeraXPrettyPrinter
  val parser = KeYmaeraXParser

  def parseShouldBe(input: String, expr: Expression) = {
    val parse = parser(input)
    if (!(parse == expr)) {
      println("Reparsing" +
        "\nInput:      " + input +
        "\nParsed:     " + parse + " @ " + parse.getClass.getSimpleName +
        "\nExpression: " + KeYmaeraXPrettyPrinter.fullPrinter(parse))
      parse should be(expr)
    }
  }

  "The parser" should "reparse pretty-prints of random formulas" in {
    for (i <- 1 to randomTrials) {
      val e = rand.nextFormula(randomComplexity)
      val printed = pp.stringify(e)
      println("Random in: " + printed)
      val full = pp.fullPrinter(e)
      println("Fullform:  " + full)
      parseShouldBe(full, e)
      println("Reparsing: " + printed)
      parseShouldBe(printed, e)
    }
  }

}
