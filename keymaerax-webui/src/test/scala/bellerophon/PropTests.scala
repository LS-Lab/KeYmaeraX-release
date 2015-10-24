package bellerophon

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import org.scalatest.{FlatSpec, Matchers}
import edu.cmu.cs.ls.keymaerax.btactics.PropositionalTactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

import scala.collection.immutable.IndexedSeq

/**
 * Tests of the propositional sequent calculus tactics.
 * @author Nathan Fulton
 */
class PropTests extends FlatSpec with Matchers {
  val sinterp = new SequentialInterpreter()

  "AndRTopLevel" should "map |- 1=1 & True to |- True ; |- True" in {
    val tactic = AndRTopLevel(FormulaListType())
    val f      = And("1=1".asFormula, True)
    val result = sinterp(tactic, BelleProvable(Provable.startProof(f)))

    val expectedSubgoals =
      (new Sequent(Nil, IndexedSeq(), IndexedSeq("1=1".asFormula))) ::
      (new Sequent(Nil, IndexedSeq(), IndexedSeq(True))) ::
      Nil

    result.isInstanceOf[BelleProvable] shouldBe true
    result.asInstanceOf[BelleProvable].p.subgoals shouldBe expectedSubgoals
  }

  "AndR" should "map |- true, 1=1 & true, 2=2 correctly" in {
    val tactic = AndR
      .apply(FormulaListType())
      .apply(FormulaListType(Seq(True)))
      .apply(FormulaListType(Seq("2=2".asFormula)))

    val f = And("1=1".asFormula, True)
    val result = sinterp(tactic, BelleProvable(Provable.startProof(f)))

    result.isInstanceOf[BelleProvable] shouldBe true
  }
}
