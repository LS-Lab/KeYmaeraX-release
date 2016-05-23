/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.btactics.{RandomFormula, StaticSemanticsTools}
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXPrettyPrinter}
import testHelper.KeYmaeraXTestTags.{CheckinTest, SlowTest, SummaryTest, UsualTest}
import scala.collection.immutable

import scala.collection.immutable._
import org.scalatest.{FlatSpec, Matchers, PrivateMethodTester}

/**
 * Tests printing for no pretty printer.
  *
 * @author Andre Platzer
 */
class NoPrinterScala extends FlatSpec with Matchers {
  val randomTrials = 4000
  val randomComplexity = 10
  val rand = new RandomFormula()

  "No Pretty Printer" should "use default printer" in {print(PrettyPrinter.printer(Number(9)))}

  it should "printing should give some output even if boring" in {test()}

  private def test(randomTrials: Int= randomTrials, randomComplexity: Int = randomComplexity) =
    for (i <- 1 to randomTrials) {
      val e = rand.nextExpression(randomComplexity)
      println("Random: " + e)
      println("Of class: " + e.getClass)
      println("Of kind: " + e.kind)
      println("Of sort: " + e.sort)
    }

}
