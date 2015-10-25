package bellerophon

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Idioms
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._
import edu.cmu.cs.ls.keymaerax.core.{Formula, Sequent, SuccPos, Provable}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import scala.collection.immutable.IndexedSeq
import org.scalatest.{Matchers, FlatSpec}

/**
 * Very fine-grained tests of the sequential interpreter.
 * These tests are all I/O tests, so it should be possible to switch out
 * theInterpreter when other interpreters are implemented.
 * @author Nathan Fulton
 */
class SequentialInterpreterTests extends FlatSpec with Matchers {
  val theInterpreter = SequentialInterpreter()

  "AndR" should "prove |- 1=1 ^ 2=2" in {
    val tactic = AndR(SuccPos(0))
    val v = {
      val f = "1=1 & 2=2".asFormula
      BelleProvable(Provable.startProof(f))
    }
    val result = theInterpreter.apply(tactic, v)

    val expectedResult = Seq(
      Sequent(Nil, IndexedSeq(), IndexedSeq("1=1".asFormula)),
      Sequent(Nil, IndexedSeq(), IndexedSeq("2=2".asFormula))
    )

    result.isInstanceOf[BelleProvable] shouldBe true
    result.asInstanceOf[BelleProvable].p.subgoals shouldBe expectedResult
  }

  "Sequential Combinator" should "prove |- 1=2 -> 1=2" in {
    val tactic = ImplyR(SuccPos(0)) & TrivialCloser
    val v = {
      val f = "1=2 -> 1=2".asFormula
      BelleProvable(Provable.startProof(f))
    }
    val result = theInterpreter.apply(tactic, v)

    result.isInstanceOf[BelleProvable] shouldBe true
    result.asInstanceOf[BelleProvable].p.isProved shouldBe true
  }

  "Either combinator" should "prove |- 1=2 -> 1=2 by AndR | (ImplyR & Close)" in {
    val tactic = AndR(SuccPos(0)) | (ImplyR(SuccPos(0)) & TrivialCloser)
    val v = {
      val f = "1=2 -> 1=2".asFormula
      BelleProvable(Provable.startProof(f))
    }
    val result = theInterpreter.apply(tactic, v)

    result.isInstanceOf[BelleProvable] shouldBe true
    result.asInstanceOf[BelleProvable].p.isProved shouldBe true
  }

  it should "prove |- 1=2 -> 1=2 by (ImplyR & Close) | AndR" in {
    val tactic = (ImplyR(SuccPos(0)) & TrivialCloser) | AndR(SuccPos(0))
    val v = {
      val f = "1=2 -> 1=2".asFormula
      BelleProvable(Provable.startProof(f))
    }
    val result = theInterpreter.apply(tactic, v)

    result.isInstanceOf[BelleProvable] shouldBe true
    result.asInstanceOf[BelleProvable].p.isProved shouldBe true
  }

  "DoAll combinator" should "prove |- (1=1->1=1) & (2=2->2=2)" in {
    val f = "(1=1->1=1) & (2=2->2=2)".asFormula
    val expr = AndR(SuccPos(0)) & DoAll (ImplyR(SuccPos(0)) & TrivialCloser)
    shouldClose(expr, f)
  }

  it should "move inside Eithers correctly" in {
    val f = "(1=1->1=1) & (2=2->2=2)".asFormula
    val expr = AndR(SuccPos(0)) & DoAll (AndR(SuccPos(0)) | (ImplyR(SuccPos(0)) & TrivialCloser))
    shouldClose(expr, f)
  }

  "* combinator" should "prove |- (1=1->1=1) & (2=2->2=2)" in {
    val f = "(1=1->1=1) & (2=2->2=2)".asFormula
    val expr = (
      DoAll(AndR(SuccPos(0))) |
      DoAll(ImplyR(SuccPos(0)) & TrivialCloser)
    )*@(TheType())
  }

  "Branch Combinator" should "prove |- (1=1->1=1) & (2=2->2=2)" in {
    val tactic = AndR(SuccPos(0)) < (
      ImplyR(SuccPos(0)) & TrivialCloser,
      ImplyR(SuccPos(0)) & TrivialCloser
    )
    val v = {
      val f = "(1=1->1=1) & (2=2->2=2)".asFormula
      BelleProvable(Provable.startProof(f))
    }
    val result = theInterpreter.apply(tactic, v)

    result.isInstanceOf[BelleProvable] shouldBe true
    result.asInstanceOf[BelleProvable].p.isProved shouldBe true
  }

  it should "handle cases were subgoals are added." in {
    val tactic = AndR(SuccPos(0)) < (
      AndR(SuccPos(0)),
      ImplyR(SuccPos(0)) & TrivialCloser
    )
    val f = "(2=2 & 3=3) & (1=1->1=1)".asFormula
    shouldResultIn(
      tactic,
      f,
      Seq(toSequent("2=2"), toSequent("3=3"))
    )
  }

  it should "handle cases were subgoals are added -- switch order" in {
    val tactic = AndR(SuccPos(0)) < (
      ImplyR(SuccPos(0)) & TrivialCloser,
      AndR(SuccPos(0))
      )
    val f = "(1=1->1=1) & (2=2 & 3=3)".asFormula
    shouldResultIn(
      tactic,
      f,
      Seq(toSequent("2=2"), toSequent("3=3"))
    )
  }

  "Unification" should "work on 1=1->1=1" in {
    val pattern = SequentType(toSequent("p() -> p()"))
    val e = USubstPatternTactic(Seq((pattern, ImplyR(SuccPos(0)) & TrivialCloser)))
    shouldClose(e, "1=1->1=1".asFormula)
  }

  it should "work when there are non-working patterns" in {
    val pattern1 = SequentType(toSequent("p() -> p()"))
    val pattern2 = SequentType(toSequent("p() & q()"))
    val e = USubstPatternTactic(Seq(
      (pattern2, ErrorT("Should never get here.")),
      (pattern1, ImplyR(SuccPos(0)) & TrivialCloser)
    ))
    shouldClose(e, "1=1->1=1".asFormula)
  }

  it should "work when there are non-working patterns -- flipped order." in {
    val pattern1 = SequentType(toSequent("p() -> p()"))
    val pattern2 = SequentType(toSequent("p() & q()"))
    val e = USubstPatternTactic(Seq(
      (pattern1, ImplyR(SuccPos(0)) & TrivialCloser),
      (pattern2, ErrorT("Should never get here."))
    ))
    shouldClose(e, "1=1->1=1".asFormula)
  }

  it should "choose the first applicable unification when there are many options" in {
    val pattern1 = SequentType(toSequent("p() -> p()"))
    val pattern2 = SequentType(toSequent("p() -> q()"))
    val e = USubstPatternTactic(Seq(
      (pattern1, ImplyR(SuccPos(0)) & TrivialCloser),
      (pattern2, ErrorT("Should never get here."))
    ))
    shouldClose(e, "1=1->1=1".asFormula)
  }

  it should "choose the first applicable unification when there are many options -- flipped order" in {
    val pattern1 = SequentType(toSequent("p() -> p()"))
    val pattern2 = SequentType(toSequent("p() -> q()"))
    val e = USubstPatternTactic(Seq(
      (pattern2, ErrorT("Should never get here.")),
      (pattern1, ImplyR(SuccPos(0)) & TrivialCloser)
    ))
    a[BelleUserGeneratedError] shouldBe thrownBy (shouldClose(e, "1=1->1=1".asFormula))
  }

  "AtSubgoal" should "work" in {
    val t = AndR(SuccPos(0)) &
      Idioms.AtSubgoal(0, ImplyR(SuccPos(0)) & TrivialCloser) &
      Idioms.AtSubgoal(0, ImplyR(SuccPos(0)) & TrivialCloser)
    shouldClose(t, "(1=1->1=1) & (2=2->2=2)".asFormula)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Helper methods
  //////////////////////////////////////////////////////////////////////////////////////////////////

  private def toSequent(s : String) = new Sequent(Nil, IndexedSeq(), IndexedSeq(s.asFormula))

  private def shouldClose(expr: BelleExpr, f: Formula) = {
    val v = BelleProvable(Provable.startProof(f))
    val result = theInterpreter.apply(expr, v)
    result.isInstanceOf[BelleProvable] shouldBe true
    result.asInstanceOf[BelleProvable].p.isProved shouldBe true
  }

  private def shouldResultIn(expr: BelleExpr, f: Formula, expectedResult : Seq[Sequent]) = {
    val v = BelleProvable(Provable.startProof(f))
    val result = theInterpreter.apply(expr, v)
    result.isInstanceOf[BelleProvable] shouldBe true
    result.asInstanceOf[BelleProvable].p.subgoals shouldBe expectedResult
  }
}
