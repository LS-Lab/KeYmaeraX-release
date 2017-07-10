/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.tags.CheckinTest
import org.scalatest.{FlatSpec, Matchers, PrivateMethodTester}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._


/**
  * @author Nathan Fulton
  */
@CheckinTest
class UnicodeParserTests extends FlatSpec with Matchers with PrivateMethodTester {
  "The parser" should "parse conjunctions of inequalities and such" in {
    val f = "g > 0 ∧ 1 ≥ c ∧ c ≥ 0".asFormula
  }

  it should "parse disjunctions of inequalities with implications and equivalences" in {
    val f = "1=1 ∨ 2=2 → 3=3 ∨ 2=2 ↔ 3=3 ∨ 2=2 ← 3=3 ∨ ∀ eps (∃ delta (eps < delta))".asFormula
  }

  ignore should "parse unequal" in {
    val f = "1 ≠ 2".asFormula //@todo
  }

  "Tactic parser" should "parse when unicode is used as a tactic argument" in {
    val t = "cut({`g > 0 ∧ 1 ≥ c ∧ c ≥ 0`})".asTactic
  }
}
