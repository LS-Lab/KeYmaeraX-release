package bellerophon

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleProvable, SequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics._
import edu.cmu.cs.ls.keymaerax.core.{Formula, Sequent, SuccPos, Provable}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import scala.collection.immutable.IndexedSeq
import org.scalatest.{Matchers, FlatSpec}

/**
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

  //@todo test * combinator.

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
