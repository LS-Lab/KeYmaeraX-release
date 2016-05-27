package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics]]
 */
class ProofRuleTests extends TacticTestBase {

  "Axiomatic" should "support axiomatic rules" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq("[a_;]p_(??)".asFormula), immutable.IndexedSeq("[a_;]q_(??)".asFormula)),
      TactixLibrary.by("[] monotone", USubst(Nil)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "p_(??)".asFormula
    result.subgoals.head.succ should contain only "q_(??)".asFormula
  }

  it should "use the provided substitution for axiomatic rules" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq("[?x>5;]x>2".asFormula), immutable.IndexedSeq("[?x>5;]x>0".asFormula)),
      TactixLibrary.by("[] monotone",
        USubst(
          SubstitutionPair(ProgramConst("a_"), Test("x>5".asFormula))::
          SubstitutionPair("p_(??)".asFormula, "x>2".asFormula)::
          SubstitutionPair("q_(??)".asFormula, "x>0".asFormula)::Nil)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>2".asFormula
    result.subgoals.head.succ should contain only "x>0".asFormula
  }

  it should "support axioms" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq("\\forall x_ x_>0 -> z>0".asFormula)),
      TactixLibrary.by("all instantiate",
        USubst(
          SubstitutionPair(PredOf(Function("p", None, Real, Bool), DotTerm), Greater(DotTerm, "0".asTerm))::
          SubstitutionPair("f()".asTerm, "z".asTerm)::Nil)))
    result shouldBe 'proved
  }

  it should "support derived axioms" in {
    val result = proveBy(
      Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq("(!\\forall x_ x_>0) <-> (\\exists x_ !x_>0)".asFormula)),
      TactixLibrary.by("!all",
        USubst(SubstitutionPair(PredOf(Function("p_", None, Real, Bool), DotTerm), Greater(DotTerm, "0".asTerm))::Nil)))
    result shouldBe 'proved
  }

  "hideR" should "hide sole formula in succedent" in {
    val result = proveBy("a=2".asFormula, ProofRuleTactics.hideR(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ shouldBe empty
  }

  it should "hide first formula in succedent" in {
    val result = proveBy(Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq("a=2".asFormula, "b=3".asFormula)),
      ProofRuleTactics.hideR(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "b=3".asFormula
  }

  it should "hide last formula in succedent" in {
    val result = proveBy(Sequent(Nil, immutable.IndexedSeq(), immutable.IndexedSeq("a=2".asFormula, "b=3".asFormula)),
      ProofRuleTactics.hideR(2))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "a=2".asFormula
  }
}
