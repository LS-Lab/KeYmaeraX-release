/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.LazySequentialInterpreter
import edu.cmu.cs.ls.keymaerax.btactics.RandomFormula
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tagobjects.{CheckinTest, SummaryTest}
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import org.scalatest.{BeforeAndAfterAll, FlatSpec, Matchers}
import testHelper.CustomAssertions.withSafeClue
import testHelper.KeYmaeraXTestTags.{SlowTest, UsualTest}

import scala.collection.immutable._

/**
 * Instantiate generic tester for KeYmaera X formula parser
 *
 * @author
 *   Brandon Bohrer
 */
class KeYmaeraXRandomParserTests
    extends RandomParserTests(
      {
        Configuration.setConfiguration(FileConfiguration)
        if (false) KeYmaeraXParser.formulaParser else DLParser.formulaParser
      },
      new RandomFormula(),
    )
class KeYmaeraXDeterministicParserTests
    extends RandomParserTests(
      {
        Configuration.setConfiguration(FileConfiguration)
        if (false) KeYmaeraXParser.formulaParser else DLParser.formulaParser
      },
      new RandomFormula(seed = 0),
    )

/**
 * Generic parser tester, tests some parser on pretty prints of randomly generated formulas
 *
 * @author
 *   Andre Platzer
 * @author
 *   Brandon Bohrer
 */
class RandomParserTests(parser: String => Formula, rand: RandomFormula)
    extends FlatSpec with Matchers with BeforeAndAfterAll {

  private val randomTrials = 4000
  private val randomComplexity = 8
  private val pp = KeYmaeraXPrettyPrinter

  override def beforeAll(): Unit = {
    KeYmaeraXTool.init(Map(
      KeYmaeraXTool.INIT_DERIVATION_INFO_REGISTRY -> "false",
      KeYmaeraXTool.INTERPRETER -> LazySequentialInterpreter.getClass.getSimpleName,
    ))
  }

  override def afterAll(): Unit = { KeYmaeraXTool.shutdown() }

  def parseShouldBe(input: String, expr: Expression): Any = {
    val parse = parser(input)
    if (!(parse == expr)) {
      println(
        "Reparsing" + "\nInput:      " + input + "\nParsed:     " +
          KeYmaeraXPrettyPrinter(parse) + // + " @ " + parse.getClass.getSimpleName +
          "\nExpression: " + KeYmaeraXPrettyPrinter.fullPrinter(parse)
      )
      parse shouldBe expr
    }
  }

  "The parser" should "reparse pretty-prints of random formulas (checkin)" taggedAs CheckinTest in { test(10, 6) }
  it should "reparse pretty-prints of random formulas (summary)" taggedAs SummaryTest in { test(50, 6) }
  it should "reparse pretty-prints of random formulas (usual)" taggedAs UsualTest in { test(200, 10) }
  it should "reparse pretty-prints of random formulas (slow)" taggedAs SlowTest in { test(randomTrials, 20) }

  private def test(randomTrials: Int = randomTrials, randomComplexity: Int = randomComplexity): Unit =
    for (i <- 1 to randomTrials) {
      val randClue = "Formula produced in\n\t " + i + "th run of " + randomTrials +
        " random trials,\n\t generated with " + randomComplexity + " random complexity\n\t from seed " + rand.seed

      val e = withSafeClue("Error generating random formula\n\n" + randClue) { rand.nextFormula(randomComplexity) }
      val output = withSafeClue("Error printing\n\n" + randClue) { pp.stringify(e) }

      withSafeClue("Random formula " + output + "\n\n" + randClue) { reparse(e) }
    }

  private def reparse(e: Expression): Unit = {
    val printed = pp.stringify(e)
    val full = pp.fullPrinter(e)
    parseShouldBe(full, e)
    parseShouldBe(printed, e)
  }

}
