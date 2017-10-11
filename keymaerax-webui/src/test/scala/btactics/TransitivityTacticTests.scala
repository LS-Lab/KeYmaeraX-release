/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package btactics

import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary, Transitivity}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * @author Nathan Fulton
  */
class TransitivityTacticTests extends TacticTestBase {
  val setupTactic = TactixLibrary.implyR(1) & (TactixLibrary.andL('L)*)

  "Search function" should "Find result" in (withMathematica(_ => {
    val f = "a>=b & b >= c -> a >= c".asFormula
    val sequent = proveBy(f, setupTactic).subgoals(0)

    Transitivity.search(sequent) shouldBe Some(List("a >= b".asFormula, "b >= c".asFormula))
    Transitivity.searchResultToPositionList(sequent,Transitivity.search(sequent).get) shouldBe List(-1, -2)
    Transitivity.transitivityLemma(Transitivity.search(sequent).get) shouldBe "\\forall TRANS0 \\forall TRANS1 \\forall TRANS2 (TRANS0>=TRANS1&TRANS1>=TRANS2->TRANS0>=TRANS2)".asFormula

    val transitivyTacticResult = proveBy(sequent, Transitivity.closeTransitive)
    transitivyTacticResult.isProved shouldBe true
  }))

  it should "prove 3 chained inequalities" in (withMathematica(_ => {
    val f = "a>=b & b >= c & c >= d -> a >= d".asFormula
    val sequent = proveBy(f, setupTactic).subgoals(0)
    val transitivyTacticResult = proveBy(sequent, Transitivity.closeTransitive)
    transitivyTacticResult.isProved shouldBe true
  }))

  it should "prove 4 chained inequalities" in (withMathematica(_ => {
    val f = "a>=b & b >= c & c >= d & d >= e & e >= f & f >= z -> a >= z".asFormula
    val sequent = proveBy(f, setupTactic).subgoals(0)
    val transitivyTacticResult = proveBy(sequent, Transitivity.closeTransitive)
    transitivyTacticResult.isProved shouldBe true
  }))

  it should "prove 4 chained inequalities when there are extra facts around" in (withMathematica(_ => {
    val f = "a>=b & b >= c & c >= d & d >= e & e >= f & f >= z & f >= w -> a >= z".asFormula
    val sequent = proveBy(f, setupTactic).subgoals(0)
    val transitivyTacticResult = proveBy(sequent, Transitivity.closeTransitive)
    transitivyTacticResult.isProved shouldBe true
  }))

  it should "prove 4 chained inequalities when there are extra facts around about the starting term" in (withMathematica(_ => {
    val f = "a >= w & a>=b & b >= c & c >= d & d >= e & e >= f & f >= z -> a >= z".asFormula
    val sequent = proveBy(f, setupTactic).subgoals(0)
    val transitivyTacticResult = proveBy(sequent, Transitivity.closeTransitive)
    transitivyTacticResult.isProved shouldBe true
  }))

  it should "prove 4 chained inequalities when there are extra facts around about the ending term" in (withMathematica(_ => {
    val f = " w >= z & a>=b & b >= c & c >= d & d >= e & e >= f & f >= z -> a >= z".asFormula
    val sequent = proveBy(f, setupTactic).subgoals(0)
    val transitivyTacticResult = proveBy(sequent, Transitivity.closeTransitive)
    transitivyTacticResult.isProved shouldBe true
  }))
}
