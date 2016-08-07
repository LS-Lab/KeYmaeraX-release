/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.core

import scala.collection.immutable
import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.btactics.{DerivedRuleInfo, RandomFormula}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, USubstTest, UsualTest}
import edu.cmu.cs.ls.keymaerax.tools.KeYmaera
import org.scalatest._
import testHelper.KeYmaeraXTestTags
import testHelper.CustomAssertions.withSafeClue
import testHelper.KeYmaeraXTestTags.AdvocatusTest

import scala.collection.immutable.List
import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

/**
  * Uniform renaming and bound renaming clash test dummies.
  *
  * @author Andre Platzer
 */
@SummaryTest
@USubstTest
class URenameTests extends FlatSpec with Matchers {
  KeYmaera.init(Map.empty)

  "Bound renaming" should "refuse semantic renaming on p(||) UnitPredicationals" taggedAs(AdvocatusTest) in {
    /** {{{
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
    val prem = Provable.startProof(Sequent(IndexedSeq("\\forall x p(||)".asFormula), IndexedSeq("\\forall x p(||)".asFormula)))(
      Close(AntePos(0),SuccPos(0)), 0
    )
    prem shouldBe 'proved
    // assumed premise |- \forall x p(||) -> \forall y p(||)
    // unsound conclusion y>=0 |- \forall x y>=0 -> \forall y y>=0
    val conc = Provable.startProof(Sequent(IndexedSeq("y>=0".asFormula), IndexedSeq("\\forall x y>=0 -> \\forall y y>=0".asFormula)))(
      HideLeft(AntePos(0)), 0) (
      ImplyRight(SuccPos(0)), 0
    )
    conc should not be 'proved
    conc.subgoals should be (IndexedSeq(Sequent(IndexedSeq("\\forall x y>=0".asFormula), IndexedSeq("\\forall y y>=0".asFormula))))
    // bound renaming would prove unsound conc from prem if it forgets to clash on semantic renaming
    a [RenamingClashException] shouldBe thrownBy {prem(Sequent(IndexedSeq("\\forall x p(||)".asFormula), IndexedSeq("\\forall y p(||)".asFormula)),
      BoundRenaming(Variable("y"),Variable("x"), SuccPos(0))
    )}
    a [RenamingClashException] shouldBe thrownBy {
      // the following wouldBe possible if an exception ain't thrown
      val clash = prem(Sequent(IndexedSeq("\\forall x p(||)".asFormula), IndexedSeq("\\forall y p(||)".asFormula)),
        BoundRenaming(Variable("y"), Variable("x"), SuccPos(0))
      )
      // wouldBe from now on
      clash shouldBe 'proved
      clash.conclusion should be(Sequent(IndexedSeq("\\forall x p(||)".asFormula), IndexedSeq("\\forall y p(||)".asFormula)))
      val subst = clash(USubst(SubstitutionPair("p(||)".asFormula, "y>=0".asFormula) :: Nil))
      subst shouldBe 'proved
      val unsound = conc(subst, 0)
      unsound.conclusion should be(Sequent(IndexedSeq("y>=0".asFormula), IndexedSeq("\\forall x y>=0 -> \\forall y y>=0".asFormula)))
      unsound shouldBe 'proved
    }
  }

  //@todo test similar unsound conclusions from other semantic renaming


  "Uniform renaming" should "refuse semantic renaming on p(||) UnitPredicationals" taggedAs(AdvocatusTest) in {
    /** {{{
      * p(||) -> \forall x p(||)
      * ------------------------ UR unsound
      * p(||) -> \forall y p(||)
      * would imply an invalid conclusion by USR
      * x^2>=y -> \forall x x^2>=y
      * --------------------------
      * x^2>=y -> \forall y x^2>=y nonsense
      * }}}
      */
    val prem = Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("p(||) -> \\forall x p(||)".asFormula)))
    prem should not be 'proved
    a [RenamingClashException] shouldBe thrownBy {Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("p(||) -> \\forall y p(||)".asFormula)))(
      UniformRenaming(Variable("y"),Variable("x")), 0
    )}
    a [RenamingClashException] shouldBe thrownBy {
      val clash = Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("p(||) -> \\forall y p(||)".asFormula)))(
        UniformRenaming(Variable("y"),Variable("x")), 0
      )
      // wouldBe from now on
      clash.subgoals shouldBe IndexedSeq(Sequent(IndexedSeq(), IndexedSeq("p(||) -> \\forall x p(||)".asFormula)))
      clash.conclusion shouldBe (Sequent(IndexedSeq(), IndexedSeq("p(||) -> \\forall y p(||)".asFormula)))
      val unsound = clash(USubst(SubstitutionPair("p(||)".asFormula, "x^2>=y".asFormula) :: Nil))
      unsound.subgoals shouldBe IndexedSeq(Sequent(IndexedSeq(), IndexedSeq("x^2>=y -> \\forall x x^2>=y".asFormula)))
      unsound.conclusion shouldBe (Sequent(IndexedSeq(), IndexedSeq("x^2>=y -> \\forall y x^2>=y".asFormula)))
      //@todo now an extra antecedent y>=0 would make the top provable but the bottom unsound
    }
  }

  //@todo test similar unsound conclusions from other semantic renaming
}