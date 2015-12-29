package bellerophon

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.{RenUSubst, Legacy, Idioms}
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.error
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.launcher.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics
import edu.cmu.cs.ls.keymaerax.tools.KeYmaera
import scala.collection.immutable.IndexedSeq
import org.scalatest.{Matchers, FlatSpec}

import scala.language.postfixOps

/**
 * Very fine-grained tests of the sequential interpreter.
 * These tests are all I/O tests, so it should be possible to switch out
 * theInterpreter when other interpreters are implemented.
 * @author Nathan Fulton
 */
class SequentialInterpreterTests extends FlatSpec with Matchers {
  val initializingK = KeYmaera.init(Map.empty)
  val theInterpreter = SequentialInterpreter()

  "AndR" should "prove |- 1=1 ^ 2=2" in {
    val tactic = andR(1)
    val v = {
      val f = "1=1 & 2=2".asFormula
      BelleProvable(Provable.startProof(f))
    }
    val result = theInterpreter.apply(tactic, v)

    val expectedResult = Seq(
      Sequent(Nil, IndexedSeq(), IndexedSeq("1=1".asFormula)),
      Sequent(Nil, IndexedSeq(), IndexedSeq("2=2".asFormula))
    )

    result shouldBe a[BelleProvable]
    result.asInstanceOf[BelleProvable].p.subgoals shouldBe expectedResult
  }

  "Sequential Combinator" should "prove |- 1=2 -> 1=2" in {
    val tactic = implyR(1) & close
    val v = {
      val f = "1=2 -> 1=2".asFormula
      BelleProvable(Provable.startProof(f))
    }
    val result = theInterpreter.apply(tactic, v)

    result shouldBe a[BelleProvable]
    result.asInstanceOf[BelleProvable].p shouldBe 'proved
  }

  "Either combinator" should "prove |- 1=2 -> 1=2 by AndR | (ImplyR & Close)" in {
    val tactic = andR(1) | (implyR(1) & close)
    val v = {
      val f = "1=2 -> 1=2".asFormula
      BelleProvable(Provable.startProof(f))
    }
    val result = theInterpreter.apply(tactic, v)

    result shouldBe a[BelleProvable]
    result.asInstanceOf[BelleProvable].p shouldBe 'proved
  }

  it should "prove |- 1=2 -> 1=2 by (ImplyR & Close) | AndR" in {
    val tactic = (implyR(1) & close) | andR(1)
    val v = {
      val f = "1=2 -> 1=2".asFormula
      BelleProvable(Provable.startProof(f))
    }
    val result = theInterpreter.apply(tactic, v)

    result shouldBe a[BelleProvable]
    result.asInstanceOf[BelleProvable].p shouldBe 'proved
  }

  it should "failover to right whenever a non-closing and non-partial tactic is provided on the left" in {
    val tactic = implyR(1) | skip

    shouldResultIn(
      tactic,
      "1=2 -> 1=2".asFormula,
      Seq(Sequent(Nil, IndexedSeq(), IndexedSeq("1=2 -> 1=2".asFormula)))
    )
  }

  it should "fail when neither tactic manages to close the goal and also neither is partial" in {
    val tactic = implyR(1) | (skip & skip)
    val f = "1=2 -> 1=2".asFormula
    a[BelleError] should be thrownBy theInterpreter(tactic, BelleProvable(Provable.startProof(f))
    )
  }

  "DoAll combinator" should "prove |- (1=1->1=1) & (2=2->2=2)" in {
    val f = "(1=1->1=1) & (2=2->2=2)".asFormula
    val expr = andR(SuccPos(0)) & DoAll (implyR(SuccPos(0)) & close)
    shouldClose(expr, f)
  }

  it should "move inside Eithers correctly" in {
    val f = "(1=1->1=1) & (2=2->2=2)".asFormula
    val expr = andR(SuccPos(0)) & DoAll (andR(SuccPos(0)) | (implyR(SuccPos(0)) & close))
    shouldClose(expr, f)
  }

  "* combinator" should "prove |- (1=1->1=1) & (2=2->2=2)" in {
    val f = "(1=1->1=1) & (2=2->2=2)".asFormula
    val expr = (
      DoAll(andR(SuccPos(0))) |
      DoAll(implyR(SuccPos(0)) & close)
    )*@TheType()
  }

  it should "prove x=2&y=3&z=4 |- z=4" in {
    shouldClose(andL('_)*@TheType() &
      assertE("x=2".asFormula, "x=2 not at -1")(-1) & assertE("y=3".asFormula, "y=3 not at -2")(-2) &
      assertE("z=4".asFormula, "z=4 not at -3")(-3) & close,
      Sequent(Nil, IndexedSeq("x=2&y=3&z=4".asFormula), IndexedSeq("z=4".asFormula)))
  }

  it should "repeat 0 times if not applicable" in {
    shouldClose(andL('_)*@TheType() & close,
      Sequent(Nil, IndexedSeq("x=2".asFormula), IndexedSeq("x=2".asFormula)))
  }

  it should "saturate until no longer applicable" in {
    shouldClose(andL('Llast)*@TheType() &
      assertE("x=2".asFormula, "x=2 not at -1")(-1) & assertE("y=3".asFormula, "y=3 not at -2")(-2) &
      assertE("z=4|z=5".asFormula, "z=4|z=5 not at -3")(-3) & close,
      Sequent(Nil, IndexedSeq("x=2&y=3&(z=4|z=5)".asFormula), IndexedSeq("x=2".asFormula)))
  }

  it should "not try right branch when used in combination with either combinator" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("x=2&y=3&(z=4|z=5)".asFormula), IndexedSeq("x=2".asFormula)),
      ((andL('Llast)*@TheType() partial) | close)*@TheType())
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x=2".asFormula, "y=3".asFormula, "z=4 | z=5".asFormula)
    result.subgoals.head.succ should contain only "x=2".asFormula
  }

  "+ combinator" should "saturate with at least 1 repetition" in {
    val result = proveBy(Sequent(Nil, IndexedSeq("x=2&y=3&(z=4|z=5)".asFormula), IndexedSeq("x=2".asFormula)),
      andL('Llast)+@TheType())
    result.subgoals should have size 1
    result.subgoals.head.ante should contain only ("x=2".asFormula, "y=3".asFormula, "z=4 | z=5".asFormula)
    result.subgoals.head.succ should contain only "x=2".asFormula
  }

  it should "fail when not at least 1 repetition is possible" in {
    a [BelleError] should be thrownBy proveBy(Sequent(Nil, IndexedSeq("z=4|z=5".asFormula), IndexedSeq("x=2".asFormula)),
      andL('Llast)+@TheType())
  }

  it should "saturate with at least 1 repetition and try right branch in combination with either combinator" in {
    proveBy(Sequent(Nil, IndexedSeq("x=2&y=3&(z=4|z=5)".asFormula), IndexedSeq("x=2".asFormula)),
      ((andL('Llast)+@TheType() partial) | close)*@TheType()) shouldBe 'proved
  }

  "Branch Combinator" should "prove |- (1=1->1=1) & (2=2->2=2)" in {
    val tactic = andR(SuccPos(0)) < (
      implyR(SuccPos(0)) & close,
      implyR(SuccPos(0)) & close
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
    val tactic = andR(SuccPos(0)) < (
      andR(SuccPos(0)) partial,
      implyR(SuccPos(0)) & close
    )
    val f = "(2=2 & 3=3) & (1=1->1=1)".asFormula
    shouldResultIn(
      tactic,
      f,
      Seq(toSequent("2=2"), toSequent("3=3"))
    )
  }

  it should "fail whenever there's a non-partial tactic that doesn't close its goal." in {
    val tactic = andR(SuccPos(0)) < (
      andR(SuccPos(0)),
      implyR(SuccPos(0)) & close
      )
    val f = "(2=2 & 3=3) & (1=1->1=1)".asFormula
    a[BelleError] shouldBe thrownBy(
      theInterpreter.apply(tactic, BelleProvable(Provable.startProof(f)))
    )
  }

  it should "handle cases were subgoals are added -- switch order" in {
    val tactic = andR(SuccPos(0)) < (
      implyR(SuccPos(0)) & close,
      andR(SuccPos(0)) partial
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
    val e = USubstPatternTactic(Seq((pattern, (x:RenUSubst) => implyR(SuccPos(0)) & close)))
    shouldClose(e, "1=1->1=1".asFormula)
  }

  it should "work when there are non-working patterns" in {
    val pattern1 = SequentType(toSequent("p() -> p()"))
    val pattern2 = SequentType(toSequent("p() & q()"))
    val e = USubstPatternTactic(Seq(
      (pattern2, (x:RenUSubst) => error("Should never get here.")),
      (pattern1, (x:RenUSubst) => implyR(SuccPos(0)) & close)
    ))
    shouldClose(e, "1=1->1=1".asFormula)
  }

  it should "work when there are non-working patterns -- flipped order." in {
    val pattern1 = SequentType(toSequent("p() -> p()"))
    val pattern2 = SequentType(toSequent("p() & q()"))
    val e = USubstPatternTactic(Seq(
      (pattern1, (x:RenUSubst) => implyR(1) & close),
      (pattern2, (x:RenUSubst) => error("Should never get here."))
    ))
    shouldClose(e, "1=1->1=1".asFormula)
  }

  it should "choose the first applicable unification when there are many options" in {
    val pattern1 = SequentType(toSequent("p() -> p()"))
    val pattern2 = SequentType(toSequent("p() -> q()"))
    val e = USubstPatternTactic(Seq(
      (pattern1, (x:RenUSubst) => implyR(1) & close),
      (pattern2, (x:RenUSubst) => error("Should never get here."))
    ))
    shouldClose(e, "1=1->1=1".asFormula)
  }

  it should "choose the first applicable unification when there are many options -- flipped order" in {
    val pattern1 = SequentType(toSequent("p() -> p()"))
    val pattern2 = SequentType(toSequent("p() -> q()"))
    val e = USubstPatternTactic(Seq(
      (pattern2, (x:RenUSubst) => error("Should never get here.")),
      (pattern1, (x:RenUSubst) => implyR(1) & close)
    ))
    a[BelleUserGeneratedError] shouldBe thrownBy (shouldClose(e, "1=1->1=1".asFormula))
  }

  "AtSubgoal" should "work" in {
    val t = andR(1) &
      Idioms.atSubgoal(0, implyR(1) & close) &
      Idioms.atSubgoal(0, implyR(1) & close)
    shouldClose(t, "(1=1->1=1) & (2=2->2=2)".asFormula)
  }

  "Scheduled tactics" should "work" in {
    val legacyTactic = tactics.TacticLibrary.arithmeticT
    val t = Legacy.initializedScheduledTactic(DefaultConfiguration.defaultMathematicaConfig, legacyTactic)
    shouldClose(t, "1=1".asFormula)
  }

  it should "work again" in {
    val legacyTactic = tactics.TacticLibrary.arithmeticT
    val t = Legacy.initializedScheduledTactic(DefaultConfiguration.defaultMathematicaConfig, legacyTactic)
    shouldClose(t, "x = 0 -> x^2 = 0".asFormula)
  }


  it should "work for non-arith things" in {
    val legacyTactic = tactics.PropositionalTacticsImpl.AndRightT(SuccPos(0))
    val t = Legacy.initializedScheduledTactic(DefaultConfiguration.defaultMathematicaConfig, legacyTactic) < (
      implyR(SuccPos(0)) & close,
      implyR(SuccPos(0)) & close
      )
    shouldClose(t, "(1=1->1=1) & (1=2->1=2)".asFormula)
  }

  /*"A failing tactic"*/
  ignore should "print nice errors and provide a stack trace" in {
    val itFails = new BuiltInTactic("fails") {
      override def result(provable: Provable) = throw new ProverException("Fails...")
    }

    val conj = Idioms.nil & (itFails | itFails)

    // now try with defs
    def repTwo = conj*2

    def split = andR(1) <(
        repTwo,
        skip)

    val thrown = intercept[Throwable] {
      theInterpreter.apply(Idioms.nil
        & Idioms.nil
        & split
        & Idioms.nil
        & Idioms.nil, BelleProvable(Provable.startProof("1=1 & 2=2".asFormula)))
    }
    thrown.printStackTrace()
    thrown.getMessage should include ("Fails...")
    val s = thrown.getCause.getStackTrace
    //@todo works in isolation, but when run with other tests, we pick up stack trace elements of those too
    s.filter(_.getFileName == "SequentialInterpreterTests.scala").slice(0, 11).map(_.getLineNumber) shouldBe Array(280, 279, 278, 271, 271, 269, 266, 266, 263, 262, 276)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Helper methods
  //////////////////////////////////////////////////////////////////////////////////////////////////

  private def toSequent(s : String) = new Sequent(Nil, IndexedSeq(), IndexedSeq(s.asFormula))

  private def shouldClose(expr: BelleExpr, f: Formula): Unit = shouldClose(expr, Sequent(Nil, IndexedSeq(), IndexedSeq(f)))

  private def shouldClose(expr: BelleExpr, sequent: Sequent): Unit = {
    val v = BelleProvable(Provable.startProof(sequent))
    val result = theInterpreter.apply(expr, v)
    result shouldBe a[BelleProvable]
    result.asInstanceOf[BelleProvable].p shouldBe 'proved
  }

  private def shouldResultIn(expr: BelleExpr, f: Formula, expectedResult : Seq[Sequent]) = {
    val v = BelleProvable(Provable.startProof(f))
    val result = theInterpreter.apply(expr, v)
    result shouldBe a[BelleProvable]
    result.asInstanceOf[BelleProvable].p.subgoals shouldBe expectedResult
  }
}
