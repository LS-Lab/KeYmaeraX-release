/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package btactics

import edu.cmu.cs.ls.keymaerax.btactics.{DebuggingTactics, PropositionalTactics, TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.core.{And, Imply, Not, SeqPos}
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

  "Instantiated Equiv Rewriting" should "prove by a built-in tactic" in {
    val f = "((A()<->B()) & B()) -> false".asFormula
    val t = TactixLibrary.implyR(1) & TactixLibrary.andL(-1) & PropositionalTactics.equivRewriting(SeqPos(-1), SeqPos(-2))
    val result = proveBy(f,t)
    result.subgoals.length shouldBe 1
    result.subgoals(0).ante.length shouldBe 2
    result.subgoals(0).ante.last shouldBe "A()".asFormula
  }

  it should "prove by a built-in tactic succ" in {
    val f = "(A()<->B()) -> A()".asFormula
    val t = TactixLibrary.implyR(1) & PropositionalTactics.equivRewriting(SeqPos(-1), SeqPos(1))
    val result = proveBy(f,t)
    println(result.prettyString)
    result.subgoals.length shouldBe 1
    result.subgoals(0).succ.length shouldBe 1
    result.subgoals(0).succ.last shouldBe "B()".asFormula
  }

  it should "work for \\forall x p(x) <-> q() |- q()" in {
    val f = "(\\forall x (p(x) <-> q())) -> q()".asFormula
    val t = TactixLibrary.implyR(1) & PropositionalTactics.equivRewriting(SeqPos(-1),SeqPos(1))
    val result = proveBy(f,t)
    loneSucc(result) shouldBe "p(x)".asFormula
  }

  ignore should "work for \\forall x p(x) <-> q(x) |- p(z)" in {
    val f = "(\\forall x (p(x) <-> q(x))) -> p(z)".asFormula
    val t = TactixLibrary.implyR(1) & PropositionalTactics.equivRewriting(SeqPos(-1),SeqPos(1))
    val result = proveBy(f,t)
    println(result.prettyString)
    loneSucc(result) shouldBe "q(z)".asFormula
  }

  ignore should "work for \\forall x p(x) <-> q(x) |- q(z)" in {
    val f = "(\\forall x (p(x) <-> q(x))) -> q(z)".asFormula
    val t = TactixLibrary.implyR(1) & PropositionalTactics.equivRewriting(SeqPos(-1),SeqPos(1))
    val result = proveBy(f,t)
    println(result.prettyString)
    loneSucc(result) shouldBe "p(z)".asFormula
  }

  it should "work on ACAS X Cimpl example" in {
    val equiv = "\\forall rt \\forall h \\forall hoDot (Cimpl((rt,(h,hoDot)))<->\\forall t \\forall rt \\forall ht (rt=rv*t&A((t,(ht,hoDot)))->abs(r-rt)>rp|w*(h-ht) < -hp))".asFormula
    val fnApp = "Cimpl((rt,(h,hoDot)))".asFormula
    val f = Imply(equiv, fnApp)

    val t =  TactixLibrary.implyR(1) & PropositionalTactics.equivRewriting(SeqPos(-1),SeqPos(1))
    val result = proveBy(f,t)
    println(result.prettyString)
    loneSucc(result) shouldBe "\\forall t \\forall rt \\forall ht (rt=rv*t&A((t,(ht,hoDot)))->abs(r-rt)>rp|w*(h-ht) < -hp)".asFormula
  }

  it should "work on ACAS X Cimpl example 2" in {
    val equiv = "\\forall rt \\forall h \\forall hoDot (Cimpl((rt,(h,hoDot)))<->\\forall t \\forall rt \\forall ht (rt=rv*t&A((t,(ht,hoDot)))->abs(r-rt)>rp|w*(h-ht) < -hp))".asFormula
    val fnApp = "Cimpl((rt,(h,hoDot)))".asFormula
    val f = Not(And(equiv, fnApp))

    val t =  TactixLibrary.notR(1) & TactixLibrary.andL(-1) & PropositionalTactics.equivRewriting(SeqPos(-1),SeqPos(-2))
    val result = proveBy(f,t)
    println(result.prettyString)
    result.subgoals(0).ante.last shouldBe "\\forall t \\forall rt \\forall ht (rt=rv*t&A((t,(ht,hoDot)))->abs(r-rt)>rp|w*(h-ht) < -hp)".asFormula
  }

}
