/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core.{And, Imply, Not, SeqPos}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import org.scalatest.LoneElement._

/**
  * @author Nathan Fulton
  */
class EquivalenceTests extends TacticTestBase {
  "A<->B & A |- B" should "prove by rewriting A to B using equivlaence and then closeId." in {
    val f = "((A()<->B()) & A()) -> B()".asFormula
    val equivPos = -1
    val t = TactixLibrary.implyR(1) & TactixLibrary.andL(-1) /*end setup*/ & TactixLibrary.equivL(equivPos) <(
      TactixLibrary.andL(equivPos) & TactixLibrary.closeId,
      TactixLibrary.andL(equivPos) & TactixLibrary.notL('Llast).*(2) & TactixLibrary.closeId
    )

    proveBy(f,t) shouldBe 'proved
  }

  "Instantiated Equiv Rewriting" should "prove by a built-in tactic" in {
    val f = "((A()<->B()) & B()) -> false".asFormula
    val t = TactixLibrary.implyR(1) & TactixLibrary.andL(-1) & PropositionalTactics.equivRewriting(SeqPos(-1), SeqPos(-2))
    proveBy(f,t).subgoals.loneElement shouldBe "A() <-> B(), A() ==> false".asSequent
  }

  it should "prove by a built-in tactic succ" in {
    val f = "(A()<->B()) -> A()".asFormula
    val t = TactixLibrary.implyR(1) & PropositionalTactics.equivRewriting(SeqPos(-1), SeqPos(1))
    val result = proveBy(f,t).subgoals.loneElement shouldBe "A() <-> B() ==> B()".asSequent
  }

  it should "work for \\forall x p(x) <-> q() |- q()" in {
    val f = "(\\forall x (p(x) <-> q())) -> q()".asFormula
    val t = TactixLibrary.implyR(1) & PropositionalTactics.equivRewriting(SeqPos(-1),SeqPos(1))
    proveBy(f,t).subgoals.loneElement shouldBe "\\forall x (p(x) <-> q()) ==> p(x)".asSequent
  }

  it should "work for \\forall x p(x) <-> q(x) |- p(z)" in {
    val f = "(\\forall x (p(x) <-> q(x))) -> p(z)".asFormula
    val t = TactixLibrary.implyR(1) & PropositionalTactics.equivRewriting(SeqPos(-1),SeqPos(1))
    proveBy(f,t).subgoals.loneElement shouldBe "\\forall x (p(x) <-> q(x)) ==> q(z)".asSequent
  }

  it should "work for \\forall x p(x) <-> q(x) |- q(z)" in {
    val f = "(\\forall x (p(x) <-> q(x))) -> q(z)".asFormula
    val t = TactixLibrary.implyR(1) & PropositionalTactics.equivRewriting(SeqPos(-1),SeqPos(1))
    proveBy(f,t).subgoals.loneElement shouldBe "\\forall x (p(x) <-> q(x)) ==> p(z)".asSequent
  }

  it should "work on ACAS X Cimpl example" in {
    val equiv = "\\forall rt \\forall h \\forall hoDot (Cimpl((rt,(h,hoDot)))<->\\forall t \\forall rt \\forall ht (rt=rv*t&A((t,(ht,hoDot)))->abs(r-rt)>rp|w*(h-ht) < -hp))".asFormula
    val fnApp = "Cimpl((rt,(h,hoDot)))".asFormula
    val f = Imply(equiv, fnApp)

    val t =  TactixLibrary.implyR(1) & PropositionalTactics.equivRewriting(SeqPos(-1),SeqPos(1))
    proveBy(f,t).subgoals.loneElement shouldBe (equiv.prettyString + " ==> \\forall t \\forall rt \\forall ht (rt=rv*t&A((t,(ht,hoDot)))->abs(r-rt)>rp|w*(h-ht) < -hp)").asSequent
  }

  it should "work on ACAS X Cimpl example 2" in {
    val equiv = "\\forall rt \\forall h \\forall hoDot (Cimpl((rt,(h,hoDot)))<->\\forall t \\forall rt \\forall ht (rt=rv*t&A((t,(ht,hoDot)))->abs(r-rt)>rp|w*(h-ht) < -hp))".asFormula
    val fnApp = "Cimpl((rt,(h,hoDot)))".asFormula
    val f = Not(And(equiv, fnApp))

    val t =  TactixLibrary.notR(1) & TactixLibrary.andL(-1) & PropositionalTactics.equivRewriting(SeqPos(-1),SeqPos(-2))
    proveBy(f,t).subgoals.loneElement shouldBe (equiv.prettyString + ", \\forall t \\forall rt \\forall ht (rt=rv*t&A((t,(ht,hoDot)))->abs(r-rt)>rp|w*(h-ht) < -hp) ==> ").asSequent
  }

}
