package bellerophon

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, SequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics._
import edu.cmu.cs.ls.keymaerax.core.{Sequent, SuccPos, Provable}
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
}
