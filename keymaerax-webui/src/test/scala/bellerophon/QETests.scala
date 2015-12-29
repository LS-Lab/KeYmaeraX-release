package bellerophon

import btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.bellerophon.BelleError
import edu.cmu.cs.ls.keymaerax.btactics.ToolTactics
import edu.cmu.cs.ls.keymaerax.core.Sequent
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import scala.collection.immutable.IndexedSeq

/**
 * Tests [[ToolTactics.fullQE]] and [[ToolTactics.partialQE]].
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class QETests extends TacticTestBase {

  "Implicit params" should "work for Mathematica" in withMathematica { implicit qeTool =>
    proveBy("1=1".asFormula, ToolTactics.fullQE) shouldBe 'proved
  }

  "Full QE" should "prove x>0 & y>0 |- x*y>0" in withMathematica { implicit qeTool =>
    proveBy(Sequent(Nil, IndexedSeq("x>0".asFormula, "y>0".asFormula), IndexedSeq("x*y>0".asFormula)), ToolTactics.fullQE) shouldBe 'proved
  }

  it should "prove x^2<0 |-" in withMathematica { implicit qeTool =>
    proveBy(Sequent(Nil, IndexedSeq("x^2<0".asFormula), IndexedSeq()), ToolTactics.fullQE) shouldBe 'proved
  }

  it should "fail on |-" in withMathematica { implicit qeTool =>
    a [BelleError] should be thrownBy proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq()), ToolTactics.fullQE)
  }

  "Partial QE" should "not fail on |-" in withMathematica { implicit qeTool =>
    val result = proveBy(Sequent(Nil, IndexedSeq(), IndexedSeq()), ToolTactics.partialQE)
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "false".asFormula
  }

  it should "turn x^2>=0 |- y>1 into |- y>1" in withMathematica { implicit qeTool =>
    val result = proveBy(Sequent(Nil, IndexedSeq("x^2>=0".asFormula), IndexedSeq("y>1".asFormula)), ToolTactics.partialQE)
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "y>1".asFormula
  }

}
