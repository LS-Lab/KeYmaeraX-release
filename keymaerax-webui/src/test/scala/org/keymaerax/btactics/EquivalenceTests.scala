/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.core.{And, Imply, Not, SeqPos}
import org.keymaerax.parser.StringConverter._

import org.scalatest.LoneElement._

/** @author Nathan Fulton */
class EquivalenceTests extends TacticTestBase {
  "A<->B & A |- B" should "prove by rewriting A to B using equivlaence and then closeId." in withTactics {
    val f = "((A()<->B()) & A()) -> B()".asFormula
    val equivPos = -1
    val t = TactixLibrary.implyR(1) & TactixLibrary.andL(-1) /*end setup*/ &
      TactixLibrary.equivL(equivPos) <
      (
        TactixLibrary.andL(equivPos) & TactixLibrary.id,
        TactixLibrary.andL(equivPos) & TactixLibrary.notL(Symbol("Llast")).*(2) & TactixLibrary.id,
      )

    proveBy(f, t) shouldBe Symbol("proved")
  }

  "Instantiated Equiv Rewriting" should "prove by a built-in tactic" in withTactics {
    val f = "((A()<->B()) & B()) -> false".asFormula
    val t = TactixLibrary.implyR(1) & TactixLibrary.andL(-1) &
      PropositionalTactics.equivRewriting(SeqPos(-1), SeqPos(-2))
    proveBy(f, t).subgoals.loneElement shouldBe "A() <-> B(), A() ==> false".asSequent
  }

  it should "prove by a built-in tactic succ" in withTactics {
    val f = "(A()<->B()) -> A()".asFormula
    val t = TactixLibrary.implyR(1) & PropositionalTactics.equivRewriting(SeqPos(-1), SeqPos(1))
    val result = proveBy(f, t).subgoals.loneElement shouldBe "A() <-> B() ==> B()".asSequent
  }

  it should "work for \\forall x p(x) <-> q() |- q()" in withTactics {
    val f = "(\\forall x (p(x) <-> q())) -> q()".asFormula
    val t = TactixLibrary.implyR(1) & PropositionalTactics.equivRewriting(SeqPos(-1), SeqPos(1))
    proveBy(f, t).subgoals.loneElement shouldBe "\\forall x (p(x) <-> q()) ==> p(x)".asSequent
  }

  it should "work for \\forall x p(x) <-> q(x) |- p(z)" in withTactics {
    val f = "(\\forall x (p(x) <-> q(x))) -> p(z)".asFormula
    val t = TactixLibrary.implyR(1) & PropositionalTactics.equivRewriting(SeqPos(-1), SeqPos(1))
    proveBy(f, t).subgoals.loneElement shouldBe "\\forall x (p(x) <-> q(x)) ==> q(z)".asSequent
  }

  it should "work for \\forall x p(x) <-> q(x) |- q(z)" in withTactics {
    val f = "(\\forall x (p(x) <-> q(x))) -> q(z)".asFormula
    val t = TactixLibrary.implyR(1) & PropositionalTactics.equivRewriting(SeqPos(-1), SeqPos(1))
    proveBy(f, t).subgoals.loneElement shouldBe "\\forall x (p(x) <-> q(x)) ==> p(z)".asSequent
  }

}
