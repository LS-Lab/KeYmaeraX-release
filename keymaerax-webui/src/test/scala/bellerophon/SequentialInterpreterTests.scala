package bellerophon

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.{RenUSubst, Legacy, Idioms}
import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.launcher.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics
import edu.cmu.cs.ls.keymaerax.tactics.{Interpreter, Tactics}
import edu.cmu.cs.ls.keymaerax.tools.{Mathematica, KeYmaera, Z3}
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
    val tactic = andR(SuccPos(0))
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
    val tactic = implyR(SuccPos(0)) & trivialCloser
    val v = {
      val f = "1=2 -> 1=2".asFormula
      BelleProvable(Provable.startProof(f))
    }
    val result = theInterpreter.apply(tactic, v)

    result.isInstanceOf[BelleProvable] shouldBe true
    result.asInstanceOf[BelleProvable].p.isProved shouldBe true
  }

  "Either combinator" should "prove |- 1=2 -> 1=2 by AndR | (ImplyR & Close)" in {
    val tactic = andR(SuccPos(0)) | (implyR(SuccPos(0)) & trivialCloser)
    val v = {
      val f = "1=2 -> 1=2".asFormula
      BelleProvable(Provable.startProof(f))
    }
    val result = theInterpreter.apply(tactic, v)

    result.isInstanceOf[BelleProvable] shouldBe true
    result.asInstanceOf[BelleProvable].p.isProved shouldBe true
  }

  it should "prove |- 1=2 -> 1=2 by (ImplyR & Close) | AndR" in {
    val tactic = (implyR(SuccPos(0)) & trivialCloser) | andR(SuccPos(0))
    val v = {
      val f = "1=2 -> 1=2".asFormula
      BelleProvable(Provable.startProof(f))
    }
    val result = theInterpreter.apply(tactic, v)

    result.isInstanceOf[BelleProvable] shouldBe true
    result.asInstanceOf[BelleProvable].p.isProved shouldBe true
  }

  it should "failover to right whever a non-closing and non-partial tactic is provided on the left" in {
    val tactic = (implyR(SuccPos(0))) | Idioms.ident

    shouldResultIn(
      tactic,
      "1=2 -> 1=2".asFormula,
      Seq(Sequent(Nil, IndexedSeq(), IndexedSeq("1=2 -> 1=2".asFormula)))
    )
  }

  it should "fail when neither tactic manages to close the goal and also neither is partial" in {
    val tactic = (implyR(SuccPos(0))) | (Idioms.ident & Idioms.ident)
    val f = "1=2 -> 1=2".asFormula
    a[BelleError] should be thrownBy(
      theInterpreter(tactic, BelleProvable(Provable.startProof(f)))
    )
  }

  "DoAll combinator" should "prove |- (1=1->1=1) & (2=2->2=2)" in {
    val f = "(1=1->1=1) & (2=2->2=2)".asFormula
    val expr = andR(SuccPos(0)) & DoAll (implyR(SuccPos(0)) & trivialCloser)
    shouldClose(expr, f)
  }

  it should "move inside Eithers correctly" in {
    val f = "(1=1->1=1) & (2=2->2=2)".asFormula
    val expr = andR(SuccPos(0)) & DoAll (andR(SuccPos(0)) | (implyR(SuccPos(0)) & trivialCloser))
    shouldClose(expr, f)
  }

  "* combinator" should "prove |- (1=1->1=1) & (2=2->2=2)" in {
    val f = "(1=1->1=1) & (2=2->2=2)".asFormula
    val expr = (
      DoAll(andR(SuccPos(0))) |
      DoAll(implyR(SuccPos(0)) & trivialCloser)
    )*@(TheType())
  }

  "Branch Combinator" should "prove |- (1=1->1=1) & (2=2->2=2)" in {
    val tactic = andR(SuccPos(0)) < (
      implyR(SuccPos(0)) & trivialCloser,
      implyR(SuccPos(0)) & trivialCloser
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
      implyR(SuccPos(0)) & trivialCloser
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
      implyR(SuccPos(0)) & trivialCloser
      )
    val f = "(2=2 & 3=3) & (1=1->1=1)".asFormula
    a[BelleError] shouldBe thrownBy(
      theInterpreter.apply(tactic, BelleProvable(Provable.startProof(f)))
    )
  }

  it should "handle cases were subgoals are added -- switch order" in {
    val tactic = andR(SuccPos(0)) < (
      implyR(SuccPos(0)) & trivialCloser,
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
    val e = USubstPatternTactic(Seq((pattern, (x:RenUSubst) => implyR(SuccPos(0)) & trivialCloser)))
    shouldClose(e, "1=1->1=1".asFormula)
  }

  it should "work when there are non-working patterns" in {
    val pattern1 = SequentType(toSequent("p() -> p()"))
    val pattern2 = SequentType(toSequent("p() & q()"))
    val e = USubstPatternTactic(Seq(
      (pattern2, (x:RenUSubst) => error("Should never get here.")),
      (pattern1, (x:RenUSubst) => implyR(SuccPos(0)) & trivialCloser)
    ))
    shouldClose(e, "1=1->1=1".asFormula)
  }

  it should "work when there are non-working patterns -- flipped order." in {
    val pattern1 = SequentType(toSequent("p() -> p()"))
    val pattern2 = SequentType(toSequent("p() & q()"))
    val e = USubstPatternTactic(Seq(
      (pattern1, (x:RenUSubst) => implyR(SuccPos(0)) & trivialCloser),
      (pattern2, (x:RenUSubst) => error("Should never get here."))
    ))
    shouldClose(e, "1=1->1=1".asFormula)
  }

  it should "choose the first applicable unification when there are many options" in {
    val pattern1 = SequentType(toSequent("p() -> p()"))
    val pattern2 = SequentType(toSequent("p() -> q()"))
    val e = USubstPatternTactic(Seq(
      (pattern1, (x:RenUSubst) => implyR(SuccPos(0)) & trivialCloser),
      (pattern2, (x:RenUSubst) => error("Should never get here."))
    ))
    shouldClose(e, "1=1->1=1".asFormula)
  }

  it should "choose the first applicable unification when there are many options -- flipped order" in {
    val pattern1 = SequentType(toSequent("p() -> p()"))
    val pattern2 = SequentType(toSequent("p() -> q()"))
    val e = USubstPatternTactic(Seq(
      (pattern2, (x:RenUSubst) => error("Should never get here.")),
      (pattern1, (x:RenUSubst) => implyR(SuccPos(0)) & trivialCloser)
    ))
    a[BelleUserGeneratedError] shouldBe thrownBy (shouldClose(e, "1=1->1=1".asFormula))
  }

  "AtSubgoal" should "work" in {
    val t = andR(SuccPos(0)) &
      Idioms.atSubgoal(0, implyR(SuccPos(0)) & trivialCloser) &
      Idioms.atSubgoal(0, implyR(SuccPos(0)) & trivialCloser)
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
      implyR(SuccPos(0)) & trivialCloser,
      implyR(SuccPos(0)) & trivialCloser
      )
    shouldClose(t, "(1=1->1=1) & (1=2->1=2)".asFormula)
  }

  "A failing tactic" should "print nice errors and provide a stack trace" in {
    val itFails = new BuiltInTactic("fails") {
      override def result(provable: Provable) = throw new ProverException("Fails...")
    }

    val conj = Idioms.nil & (itFails | itFails)

    // now try with defs
    def repTwo = conj*2

    def split = (andR(1) <(
        repTwo,
        Idioms.ident partial)
      )*@TheType()

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
    s.filter(_.getFileName == "SequentialInterpreterTests.scala").slice(0, 11).map(_.getLineNumber) shouldBe Array(266, 265, 264, 259, 256, 256, 254, 251, 251, 248, 247)
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
