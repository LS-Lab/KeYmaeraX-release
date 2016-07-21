/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package btactics

import edu.cmu.cs.ls.keymaerax.btactics.{DebuggingTactics, PropositionalTactics, TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
  * @author Nathan Fulton
  */
class EquivalenceTests extends TacticTestBase {
  "A<->B & A |- B" should "prove by rewriting A to B using equivlaence and then closeId." in {
    val f = "((A()<->B()) & A()) -> B()".asFormula
    val equivPos = -1
    val succPos = 1
    val t = TactixLibrary.implyR(1) & TactixLibrary.andL(-1) /*end setup*/ & TactixLibrary.equivL(equivPos) <(
      TactixLibrary.andL(equivPos) & TactixLibrary.closeId,
      TactixLibrary.andL(equivPos) & TactixLibrary.notL('Llast).*(2) & TactixLibrary.closeId
    )

    val result = proveBy(f,t)
    println(result.prettyString)

    result shouldBe 'proved
  }

  it should "prove by a built-in tactic" in {
    val f = "((A()<->B()) & B()) -> false".asFormula
    val t = TactixLibrary.implyR(1) & TactixLibrary.andL(-1) & PropositionalTactics.equivRewriting(-1, -2)
    val result = proveBy(f,t)
    result.subgoals.length shouldBe 1
    result.subgoals(0).ante.length shouldBe 2
    result.subgoals(0).ante.last shouldBe "A()".asFormula
  }

  it should "prove by a built-in tactic succ" in {
    val f = "(A()<->B()) -> A()".asFormula
    val t = TactixLibrary.implyR(1) & PropositionalTactics.equivRewriting(-1, 1)
    val result = proveBy(f,t)
    println(result.prettyString)
    result.subgoals.length shouldBe 1
    result.subgoals(0).succ.length shouldBe 1
    result.subgoals(0).succ.last shouldBe "B()".asFormula
  }
}
