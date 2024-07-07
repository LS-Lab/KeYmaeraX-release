/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.bellerophon.Find
import org.keymaerax.core._
import org.keymaerax.parser.StringConverter._
import org.keymaerax.btactics.macros.ProvableInfo
import org.keymaerax.infrastruct.SuccPosition
import org.scalatest.LoneElement._

import scala.collection.immutable._
import org.scalatest.OptionValues._

/** Tests [[org.keymaerax.btactics.ProofRuleTactics]] */
class ProofRuleTests extends TacticTestBase {

  "Axiomatic" should "support axiomatic rules" in withQE { _ =>
    val result =
      proveBy("[a_;]p_(||) ==> [a_;]q_(||)".asSequent, TactixLibrary.by(ProvableInfo("[] monotone"), USubst(Nil)))
    result.subgoals.loneElement shouldBe "p_(||) ==> q_(||)".asSequent
  }

  it should "use the provided substitution for axiomatic rules" in withQE { _ =>
    val result = proveBy(
      "[?x>5;]x>2 ==> [?x>5;]x>0".asSequent,
      TactixLibrary.by(
        ProvableInfo("[] monotone"),
        USubst(
          SubstitutionPair(ProgramConst("a_"), Test("x>5".asFormula)) ::
            SubstitutionPair("p_(||)".asFormula, "x>2".asFormula) ::
            SubstitutionPair("q_(||)".asFormula, "x>0".asFormula) :: Nil
        ),
      ),
    )
    result.subgoals.loneElement shouldBe "x>2 ==> x>0".asSequent
  }

  it should "support axioms" in withTactics {
    val result = proveBy(
      "==> \\forall x_ x_>0 -> z>0".asSequent,
      TactixLibrary.by(
        Ax.allInst,
        USubst(
          SubstitutionPair(PredOf(Function("p", None, Real, Bool), DotTerm()), Greater(DotTerm(), "0".asTerm)) ::
            SubstitutionPair("f()".asTerm, "z".asTerm) :: Nil
        ),
      ),
    )
    result shouldBe Symbol("proved")
  }

  it should "support derived axioms" in withTactics {
    val theSubst =
      USubst(SubstitutionPair(UnitPredicational("p_", AnyArg), Greater("x_".asVariable, "0".asTerm)) :: Nil)

    val result = proveBy(
      "==> (!\\forall x_ x_>0) <-> (\\exists x_ !x_>0)".asSequent,
      TactixLibrary.by(
        Ax.notAll, // (!\forall x (p(||))) <-> \exists x (!p(||))
        theSubst,
      ),
    )

    result shouldBe Symbol("proved")
  }

  import SequentCalculus._
  "hideR" should "hide sole formula in succedent" in withTactics {
    val result = proveBy("a=2".asFormula, hideR(1))
    result.subgoals.loneElement shouldBe Sequent(IndexedSeq(), IndexedSeq())
  }

  it should "hide first formula in succedent" in withTactics {
    proveBy("==> a=2, b=3".asSequent, hideR(1)).subgoals.loneElement shouldBe "==> b=3".asSequent
  }

  it should "hide last formula in succedent" in withTactics {
    proveBy("==> a=2, b=3".asSequent, hideR(2)).subgoals.loneElement shouldBe "==> a=2".asSequent
  }

  it should "hide verbatim occurrences of definitions" in withTactics {
    proveBy(
      "==> p(), q()".asSequent,
      hideR(Find(
        0,
        Some("p()".asFormula),
        SuccPosition.base0(0),
        exact = true,
        "p() ~> 0>1 :: q() ~> 1>0 :: nil".asDeclaration,
      )),
    ).subgoals.loneElement shouldBe "==> q()".asSequent
  }

  it should "try to expand definitions" in withTactics {
    proveBy(
      "==> 0>1, 1>0".asSequent,
      hideR(Find(
        0,
        Some("p()".asFormula),
        SuccPosition.base0(0),
        exact = true,
        "p() ~> 0>1 :: q() ~> 1>0 :: nil".asDeclaration,
      )),
    ).subgoals.loneElement shouldBe "==> 1>0".asSequent
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
    proveByS(
      "x>=2 <-> x>=3 ==>".asSequent,
      equivL(-1),
      _.value should contain theSameElementsAs "x>=2&x>=3::!x>=2&!x>=3".asLabels,
    )
  }

  it should "provide labels for equivR" in withTactics {
    proveByS(
      "==> x>=2 <-> x>=3".asSequent,
      equivR(1),
      _.value should contain theSameElementsAs "x>=2&x>=3::!x>=2&!x>=3".asLabels,
    )
  }

  it should "not label when only a single subgoal" in withTactics {
    proveBy("x>=2 -> x>=3".asFormula, implyR(1), _ shouldBe empty)
  }

  "Bound renaming" should "rename quantified variables" in withTactics {
    proveBy("\\forall x x>0 ==> ".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(-1))
      .subgoals
      .loneElement shouldBe "\\forall y y>0 ==> ".asSequent
  }

  it should "rename assigned variables" in withTactics {
    proveBy("==> [x:=2;]x>0".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(1)).subgoals.loneElement shouldBe
      "==> [y:=2;]y>0".asSequent
  }

  it should "rename quantified differential symbols" in withTactics {
    proveBy("==> \\forall x' x'>0".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(1))
      .subgoals
      .loneElement shouldBe "==> \\forall y' y'>0".asSequent
    proveBy("x=5 ==> \\forall x' x'>0".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(1))
      .subgoals
      .loneElement shouldBe "x=5 ==> \\forall y' y'>0".asSequent
    proveBy("==> \\forall x' (f(x))'>0".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(1))
      .subgoals
      .loneElement shouldBe "y=x ==> \\forall y' (f(y))'>0".asSequent
    proveBy("x=5 ==> \\forall x' (f(x))'>0".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(1))
      .subgoals
      .loneElement shouldBe "x=5, y=x ==> \\forall y' (f(y))'>0".asSequent
  }

  it should "rename quantified differential symbols in antecedent" in withTactics {
    proveBy("\\forall x' x'>0 ==>".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(-1))
      .subgoals
      .loneElement shouldBe "\\forall y' y'>0 ==>".asSequent
    proveBy("x=5, \\forall x' x'>0 ==>".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(-2))
      .subgoals
      .loneElement shouldBe "x=5, \\forall y' y'>0 ==>".asSequent
    proveBy("\\forall x' (f(x))'>0 ==>".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(-1))
      .subgoals
      .loneElement shouldBe "y=x, \\forall y' (f(y))'>0 ==>".asSequent
    proveBy("\\forall x' (f(x))'>0, x=5 ==>".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(-1))
      .subgoals
      .loneElement shouldBe "x=5, y=x, \\forall y' (f(y))'>0 ==>".asSequent
  }

  it should "rename nested quantified differential symbols/variables" in withTactics {
    proveBy("\\forall x' \\forall x (f(x))'>x ==>".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(-1))
      .subgoals
      .loneElement shouldBe "\\forall y' \\forall y (f(y))'>y ==>".asSequent
    proveBy("\\forall x \\forall x' (f(x))'>x ==>".asSequent, ProofRuleTactics.boundRenameAt("y".asVariable)(-1))
      .subgoals
      .loneElement shouldBe "\\forall y \\forall y' (f(y))'>y ==>".asSequent
    proveBy(
      "\\forall x \\forall x' (f(x))'>x ==>".asSequent,
      ProofRuleTactics.boundRenameAt("y".asVariable)(-1, 0 :: Nil),
    ).subgoals.loneElement shouldBe "\\forall x \\exists y (y=x & \\forall y' (f(y))'>y) ==>".asSequent
  }
}
