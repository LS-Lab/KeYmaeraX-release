package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.macros.ProvableInfo
import org.scalatest.LoneElement._

import scala.collection.immutable
import org.scalatest.OptionValues._

/**
 * Tests [[edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics]]
 */
class ProofRuleTests extends TacticTestBase {

  "Axiomatic" should "support axiomatic rules" in withQE { _ =>
    val result = proveBy("[a_;]p_(||) ==> [a_;]q_(||)".asSequent,
      TactixLibrary.by(ProvableInfo("[] monotone"), USubst(Nil)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "p_(||)".asFormula
    result.subgoals.head.succ should contain only "q_(||)".asFormula
  }

  it should "use the provided substitution for axiomatic rules" in withQE { _ =>
    val result = proveBy("[?x>5;]x>2 ==> [?x>5;]x>0".asSequent,
      TactixLibrary.by(ProvableInfo("[] monotone"),
        USubst(
          SubstitutionPair(ProgramConst("a_"), Test("x>5".asFormula))::
          SubstitutionPair("p_(||)".asFormula, "x>2".asFormula)::
          SubstitutionPair("q_(||)".asFormula, "x>0".asFormula)::Nil)))
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only "x>2".asFormula
    result.subgoals.head.succ should contain only "x>0".asFormula
  }

  it should "support axioms" in withTactics {
    val result = proveBy("==> \\forall x_ x_>0 -> z>0".asSequent,
      TactixLibrary.by(Ax.allInst,
        USubst(
          SubstitutionPair(PredOf(Function("p", None, Real, Bool), DotTerm()), Greater(DotTerm(), "0".asTerm))::
          SubstitutionPair("f()".asTerm, "z".asTerm)::Nil)))
    result shouldBe 'proved
  }

  it should "support derived axioms" in withTactics {
    val theSubst = USubst(SubstitutionPair(UnitPredicational("p_", AnyArg), Greater("x_".asVariable, "0".asTerm))::Nil)

    val result = proveBy("==> (!\\forall x_ x_>0) <-> (\\exists x_ !x_>0)".asSequent,
      TactixLibrary.by(Ax.notAll, //(!\forall x (p(||))) <-> \exists x (!p(||))
        theSubst))

    result shouldBe 'proved
  }

  import SequentCalculus._
  "hideR" should "hide sole formula in succedent" in withTactics {
    val result = proveBy("a=2".asFormula, hideR(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ shouldBe empty
  }

  it should "hide first formula in succedent" in withTactics {
    val result = proveBy(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("a=2".asFormula, "b=3".asFormula)),
      hideR(1))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "b=3".asFormula
  }

  it should "hide last formula in succedent" in withTactics {
    val result = proveBy(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("a=2".asFormula, "b=3".asFormula)),
      hideR(2))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "a=2".asFormula
  }

  "Automatic core tactics labelling" should "provide labels for andR" in withTactics {
    proveBy("x>=2 & x>=3".asFormula, andR(1), _.value should contain theSameElementsAs "x>=2::x>=3".asLabels)
  }

  it should "provide labels for orL" in withTactics {
    proveByS("x>=2 | x>=3 ==>".asSequent, orL(-1), _.value should contain theSameElementsAs "x>=2::x>=3".asLabels)
  }

  it should "provide labels for implyL" in withTactics {
    proveByS("x>=2 -> x>=3 ==>".asSequent, implyL(-1), _.value should contain theSameElementsAs "x>=2::x>=3".asLabels)
  }

  it should "provide labels for equivL" in withTactics {
    proveByS("x>=2 <-> x>=3 ==>".asSequent, equivL(-1), _.value should contain theSameElementsAs "x>=2&x>=3::!x>=2&!x>=3".asLabels)
  }

  it should "provide labels for equivR" in withTactics {
    proveByS("==> x>=2 <-> x>=3".asSequent, equivR(1), _.value should contain theSameElementsAs "x>=2&x>=3::!x>=2&!x>=3".asLabels)
  }

  it should "not label when only a single subgoal" in withTactics {
    proveBy("x>=2 -> x>=3".asFormula, implyR(1), _ shouldBe empty)
  }

  "Bound renaming" should "rename quantified variables" in withTactics {
    proveBy("\\forall x x>0 ==> ".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(-1)).
      subgoals.loneElement shouldBe "\\forall y y>0 ==> ".asSequent
  }

  it should "rename assigned variables" in withTactics {
    proveBy("==> [x:=2;]x>0".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(1)).
      subgoals.loneElement shouldBe "==> [y:=2;]y>0".asSequent
  }

  it should "rename quantified differential symbols" in withTactics {
    proveBy("==> \\forall x' x'>0".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(1)).
      subgoals.loneElement shouldBe "==> \\forall y' y'>0".asSequent
    proveBy("x=5 ==> \\forall x' x'>0".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(1)).
      subgoals.loneElement shouldBe "x=5 ==> \\forall y' y'>0".asSequent
    proveBy("==> \\forall x' (f(x))'>0".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(1)).
      subgoals.loneElement shouldBe "y=x ==> \\forall y' (f(y))'>0".asSequent
    proveBy("x=5 ==> \\forall x' (f(x))'>0".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(1)).
      subgoals.loneElement shouldBe "x=5, y=x ==> \\forall y' (f(y))'>0".asSequent
  }

  it should "rename quantified differential symbols in antecedent" in withTactics {
    proveBy("\\forall x' x'>0 ==>".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(-1)).
      subgoals.loneElement shouldBe "\\forall y' y'>0 ==>".asSequent
    proveBy("x=5, \\forall x' x'>0 ==>".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(-2)).
      subgoals.loneElement shouldBe "x=5, \\forall y' y'>0 ==>".asSequent
    proveBy("\\forall x' (f(x))'>0 ==>".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(-1)).
      subgoals.loneElement shouldBe "y=x, \\forall y' (f(y))'>0 ==>".asSequent
    proveBy("\\forall x' (f(x))'>0, x=5 ==>".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(-1)).
      subgoals.loneElement shouldBe "x=5, y=x, \\forall y' (f(y))'>0 ==>".asSequent
  }

  it should "rename nested quantified differential symbols/variables" in withTactics {
    proveBy("\\forall x' \\forall x (f(x))'>x ==>".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(-1)).
      subgoals.loneElement shouldBe "\\forall y' \\forall y (f(y))'>y ==>".asSequent
    proveBy("\\forall x \\forall x' (f(x))'>x ==>".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(-1)).
      subgoals.loneElement shouldBe "\\forall y \\forall y' (f(y))'>y ==>".asSequent
    proveBy("\\forall x \\forall x' (f(x))'>x ==>".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(-1, 0::Nil)).
      subgoals.loneElement shouldBe "\\forall x \\exists y (y=x & \\forall y' (f(y))'>y) ==>".asSequent
  }
}
