/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.btactics.RandomFormula
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers

/**
 * Tests printing for no pretty printer.
 *
 * @author
 *   Andre Platzer
 */
class NoPrinter extends AnyFlatSpec with Matchers {
  val randomTrials = 4000
  val randomComplexity = 10
  val rand = new RandomFormula()

  "No Pretty Printer" should "use default printer" in { PrettyPrinter.printer(Number(9)) }

  it should "printing should give some output even if boring" in { test() }

  private def test(randomTrials: Int = randomTrials, randomComplexity: Int = randomComplexity): Unit =
    for (i <- 1 to randomTrials) {
      val e = rand.nextExpression(randomComplexity)
      e.toString should not be empty
      e.getClass.toString should not be empty
      e.kind.toString should not be empty
      e.sort.toString should not be empty
    }

}
