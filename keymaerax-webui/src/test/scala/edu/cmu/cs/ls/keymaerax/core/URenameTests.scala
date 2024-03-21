/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.btactics.{Ax, TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.infrastruct.RenUSubst
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tagobjects.AdvocatusTest
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, USubstTest}
import org.scalatest.LoneElement._

import scala.collection.immutable._

/**
 * Uniform renaming and bound renaming clash test dummies.
 *
 * @author
 *   Andre Platzer
 */
@SummaryTest @USubstTest
class URenameTests extends TacticTestBase(registerAxTactics = Some("z3")) {

  "Bound renaming" should "refuse semantic renaming on p(||) UnitPredicationals" taggedAs AdvocatusTest in {

    /**
     * {{{
     *                 *
     * ---------------------------------- id
     * \forall x p(||) |- \forall x p(||)
     * ----------------------------------- BR unsound
     * \forall x p(||) |- \forall y p(||)
     * --------------------------------------- US
     * \forall x y>=0 |- \forall y y>=0
     * --------------------------------------- implyR(1)
     * |- \forall x y>=0 -> \forall y y>=0
     * ---------------------------------------- hide(-1)
     * y>=0 |- \forall x y>=0 -> \forall y y>=0 nonsense
     * }}}
     */
    // proved premise |- \forall x p(||) -> \forall x p(||)
    val prem = ProvableSig.startPlainProof(
      Sequent(IndexedSeq("\\forall x p(||)".asFormula), IndexedSeq("\\forall x p(||)".asFormula))
    )(Close(AntePos(0), SuccPos(0)), 0)
    prem shouldBe Symbol("proved")
    // assumed premise |- \forall x p(||) -> \forall y p(||)
    // unsound conclusion y>=0 |- \forall x y>=0 -> \forall y y>=0
    val conc = ProvableSig.startPlainProof(
      Sequent(IndexedSeq("y>=0".asFormula), IndexedSeq("\\forall x y>=0 -> \\forall y y>=0".asFormula))
    )(HideLeft(AntePos(0)), 0)(ImplyRight(SuccPos(0)), 0)
    conc should not be Symbol("proved")
    conc.subgoals should
      be(IndexedSeq(Sequent(IndexedSeq("\\forall x y>=0".asFormula), IndexedSeq("\\forall y y>=0".asFormula))))
    // bound renaming would prove unsound conc from prem if it forgets to clash on semantic renaming
    a[RenamingClashException] shouldBe thrownBy {
      prem(
        Sequent(IndexedSeq("\\forall x p(||)".asFormula), IndexedSeq("\\forall y p(||)".asFormula)),
        BoundRenaming(Variable("y"), Variable("x"), SuccPos(0)),
      )
    }
    a[RenamingClashException] shouldBe thrownBy {
      // the following wouldBe possible if an exception ain't thrown
      val clash = prem(
        Sequent(IndexedSeq("\\forall x p(||)".asFormula), IndexedSeq("\\forall y p(||)".asFormula)),
        BoundRenaming(Variable("y"), Variable("x"), SuccPos(0)),
      )
      // wouldBe from now on
      clash shouldBe Symbol("proved")
      clash.conclusion should
        be(Sequent(IndexedSeq("\\forall x p(||)".asFormula), IndexedSeq("\\forall y p(||)".asFormula)))
      val subst = clash(USubst(SubstitutionPair("p(||)".asFormula, "y>=0".asFormula) :: Nil))
      subst shouldBe Symbol("proved")
      val unsound = conc(subst, 0)
      unsound.conclusion should
        be(Sequent(IndexedSeq("y>=0".asFormula), IndexedSeq("\\forall x y>=0 -> \\forall y y>=0".asFormula)))
      unsound shouldBe Symbol("proved")
    }
  }

  // @todo test similar unsound conclusions from other semantic renaming

  "Uniform renaming" should "refuse semantic renaming on p(||) UnitPredicationals" taggedAs AdvocatusTest in {

    /**
     * {{{
     * p(||) -> \forall x p(||)
     * ------------------------ UR unsound
     * p(||) -> \forall y p(||)
     * would imply an invalid conclusion by USR
     * x^2>=y -> \forall x x^2>=y
     * --------------------------
     * x^2>=y -> \forall y x^2>=y nonsense
     * }}}
     */
    val prem = ProvableSig.startPlainProof(Sequent(IndexedSeq(), IndexedSeq("p(||) -> \\forall x p(||)".asFormula)))
    prem should not be Symbol("proved")
    a[RenamingClashException] shouldBe thrownBy {
      ProvableSig.startPlainProof(Sequent(IndexedSeq(), IndexedSeq("p(||) -> \\forall y p(||)".asFormula)))(
        UniformRenaming(Variable("y"), Variable("x")),
        0,
      )
    }
    a[RenamingClashException] shouldBe thrownBy {
      val clash = ProvableSig.startPlainProof(Sequent(IndexedSeq(), IndexedSeq("p(||) -> \\forall y p(||)".asFormula)))(
        UniformRenaming(Variable("y"), Variable("x")),
        0,
      )
      // wouldBe from now on
      clash.subgoals shouldBe IndexedSeq(Sequent(IndexedSeq(), IndexedSeq("p(||) -> \\forall x p(||)".asFormula)))
      clash.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("p(||) -> \\forall y p(||)".asFormula))
      val unsound = clash(USubst(SubstitutionPair("p(||)".asFormula, "x^2>=y".asFormula) :: Nil))
      unsound.subgoals shouldBe IndexedSeq(Sequent(IndexedSeq(), IndexedSeq("x^2>=y -> \\forall x x^2>=y".asFormula)))
      unsound.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("x^2>=y -> \\forall y x^2>=y".asFormula))
      // @todo now an extra antecedent y>=0 would make the top provable but the bottom unsound
    }
  }

  it should "rename conclusions forward but keep subgoals of unproved provables" in {
    val p = RenUSubst
      .UniformRenamingForward(ProvableSig.startPlainProof("[x:=*;]x>=0".asFormula), "x".asVariable, "y".asVariable)
    p.subgoals.loneElement shouldBe "==> [x:=*;]x>=0".asSequent
    p.conclusion shouldBe "==> [y:=*;]y>=0".asSequent
  }

  it should "refuse semantic renaming forward of unproved provables" in {
    the[RenamingClashException] thrownBy RenUSubst.UniformRenamingForward(
      ProvableSig.startPlainProof("[x:=*;][a;]x>=0".asFormula),
      "x".asVariable,
      "y".asVariable,
    ) should have message
      """Cannot replace semantic dependencies syntactically: ProgramConstant a
        |Renaming a via URename{x~>y}
        |in """.stripMargin
  }

  it should "allow semantic renaming forward of proved provables" in {
    val p = ProvableSig
      .startPlainProof("[a;]x>=0 -> [a;]x>=0".asFormula)(ImplyRight(SuccPos(0)), 0)(Close(AntePos(0), SuccPos(0)), 0)
    p shouldBe Symbol("proved")
    RenUSubst.UniformRenamingForward(p, "x".asVariable, "y".asVariable).conclusion shouldBe
      "==> [a;]y>=0 -> [a;]y>=0".asSequent
  }

  "Bound Renaming" should "refuse to rename = x -> y when formula cares about x'" in {
    val fml = Diamond(
      Assign(Variable("x"), DifferentialSymbol(BaseVariable("x"))),
      Equal(Variable("x"), DifferentialSymbol(BaseVariable("x"))),
    )
    a[RenamingClashException] shouldBe thrownBy { BoundRenaming(Variable("x"), Variable("y"), SuccPos(1))(fml) }
  }
  // @todo test similar unsound conclusions from other semantic renaming

  "Disallowed semantic renaming" should "refuse UnitFunctionals" in {
    a[RenamingClashException] shouldBe thrownBy {
      URename(Variable("x"), Variable("y"))(UnitFunctional("F", AnyArg, Real))
    }
  }

  it should "refuse UnitPredicationals" in {
    a[RenamingClashException] shouldBe thrownBy {
      URename(Variable("x"), Variable("y"))(UnitPredicational("P", AnyArg))
    }
  }

  it should "refuse Predicationals" in {
    a[RenamingClashException] shouldBe thrownBy {
      URename(Variable("x"), Variable("y"))(PredicationalOf(Function("P", None, Bool, Bool), True))
    }
    a[RenamingClashException] shouldBe thrownBy {
      URename(Variable("x"), Variable("y"))(
        PredicationalOf(Function("P", None, Bool, Bool), True).asInstanceOf[Expression]
      )
    }
  }

  it should "refuse ProgramConst" in {
    a[RenamingClashException] shouldBe thrownBy { URename(Variable("x"), Variable("y"))(ProgramConst("a")) }
    a[RenamingClashException] shouldBe thrownBy {
      URename(Variable("x"), Variable("y"))(ProgramConst("a").asInstanceOf[Expression])
    }
  }

  it should "refuse DifferentialProgramConst" in {
    a[RenamingClashException] shouldBe thrownBy {
      URename(Variable("x"), Variable("y"))(DifferentialProgramConst("a", AnyArg))
    }
    a[RenamingClashException] shouldBe thrownBy {
      URename(Variable("x"), Variable("y"))(DifferentialProgramConst("a", AnyArg).asInstanceOf[Expression])
    }
  }

  it should "refuse {DifferentialProgramConst}" in {
    a[RenamingClashException] shouldBe thrownBy {
      URename(Variable("x"), Variable("y"))(ODESystem(DifferentialProgramConst("a", AnyArg), True))
    }
    a[RenamingClashException] shouldBe thrownBy {
      URename(Variable("x"), Variable("y"))(
        ODESystem(DifferentialProgramConst("a", AnyArg), True).asInstanceOf[Expression]
      )
    }
  }

  it should "refuse [DifferentialProgramConst]false" in {
    a[RenamingClashException] shouldBe thrownBy {
      URename(Variable("x"), Variable("y"))(Box(ODESystem(DifferentialProgramConst("a", AnyArg), True), False))
    }
    a[RenamingClashException] shouldBe thrownBy {
      URename(Variable("x"), Variable("y"))(
        Box(ODESystem(DifferentialProgramConst("a", AnyArg), True), False).asInstanceOf[Expression]
      )
    }
  }

  it should "refuse DotFormula" in {
    a[RenamingClashException] shouldBe thrownBy { URename(Variable("x"), Variable("y"))(DotFormula) }
    a[RenamingClashException] shouldBe thrownBy {
      URename(Variable("x"), Variable("y"))(DotFormula).asInstanceOf[Expression]
    }
  }

  it should "refuse DotTerm()" in {
    URename(Variable("x"), Variable("y"))(DotTerm()) shouldBe DotTerm()
    URename(Variable("x"), Variable("y"))(DotTerm().asInstanceOf[Expression]) shouldBe DotTerm()
  }

  "Differential renaming" should "refuse to rename differential symbols without their respective base variable" taggedAs
    AdvocatusTest in {
      a[CoreException] shouldBe thrownBy {
        URename(DifferentialSymbol(Variable("x")), DifferentialSymbol(Variable("z")))("(x+y)'=x'+y'".asFormula)
      }
    }

  it should "avoid unsound renaming proofs" taggedAs AdvocatusTest in withMathematica { _ =>
//    val proof1 = Provable.axioms("*' derive product")(USubst(
//      SubstitutionPair(UnitFunctional("f",AnyArg,Real), "x".asVariable) ::
//        SubstitutionPair(UnitFunctional("g",AnyArg,Real), "y".asVariable) :: Nil))
//    proof1 shouldBe 'proved
//    proof1.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("(x+y)'=(x)'+(y)'".asFormula))
//    val proof = proof1
    import TactixLibrary._
    val proof = TactixLibrary.proveBy("(x+y)'=x'+y'".asFormula, derive(1, 0 :: Nil) & byUS(Ax.equalReflexive))
    proof shouldBe Symbol("proved")
    proof.conclusion shouldBe Sequent(IndexedSeq(), IndexedSeq("(x+y)'=x'+y'".asFormula))
    a[CoreException] shouldBe thrownBy {
      proof(UniformRenaming(DifferentialSymbol(Variable("x")), DifferentialSymbol(Variable("z"))), 0)
    }
    // this prolongation wouldBe a proof of unsound (x+y)'=z'+y'
  }
}
