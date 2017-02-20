package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleThrowable
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._

import scala.collection.immutable.IndexedSeq

/**
 * Tests [[ToolTactics.fullQE]] and [[ToolTactics.partialQE]].
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class QETests extends TacticTestBase {

  "Implicit params" should "work for Mathematica" in withMathematica { qeTool =>
    proveBy("1=1".asFormula, ToolTactics.fullQE(qeTool)) shouldBe 'proved
  }

  "Full QE" should "prove x>0 & y>0 |- x*y>0" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq("x>0".asFormula, "y>0".asFormula), IndexedSeq("x*y>0".asFormula)), ToolTactics.fullQE(qeTool)) shouldBe 'proved
  }

  it should "prove x^2<0 |-" in withMathematica { qeTool =>
    proveBy(Sequent(IndexedSeq("x^2<0".asFormula), IndexedSeq()), ToolTactics.fullQE(qeTool)) shouldBe 'proved
  }

  it should "fail on |-" in withMathematica { qeTool =>
    a [BelleThrowable] should be thrownBy proveBy(Sequent(IndexedSeq(), IndexedSeq()), ToolTactics.fullQE(qeTool))
  }

  it should "fail on parsed decimal representations" in withMathematica { qeTool =>
    proveBy("0.33333333333333 = 1/3".asFormula,ToolTactics.fullQE(qeTool)) shouldBe 'proved
  }

  it should "correct behavior (Z3)" in withZ3 { qeTool =>
    a [BelleThrowable] should be thrownBy proveBy("0.33333333333333 = 1/3".asFormula,ToolTactics.fullQE(qeTool))
  }

  it should "fail on internal decimal representations" in withMathematica { qeTool =>
    proveBy(Equal(Number(0.33333333333333),Divide(Number(1),Number(3))),ToolTactics.fullQE(qeTool)) shouldBe 'proved
  }

  it should "fail (?) on internal decimal representations (2)" in withMathematica { qeTool =>
    // This isn't as bad as the above two
    proveBy(Equal(Number(1.0),Minus(Number(4),Number(3))),ToolTactics.fullQE(qeTool)) shouldBe 'proved
  }

  it should "fail x()=x" in withMathematica { qeTool =>
    the [BelleThrowable] thrownBy proveBy("x()=x".asFormula, ToolTactics.fullQE(qeTool) & done) should have message
      """[Bellerophon Runtime] QE was unable to prove: invalid formula
        |Expected proved provable, but got NoProofTermProvable(Provable(  ==>  x()=x
        |  from     ==>  false))""".stripMargin
  }

  it should "have soundness bug with decimal representations " in withMathematica { qeTool =>

    val pr = proveBy("false".asFormula,
      cut("1-3 * 0.33333333333333 = 0".asFormula) <( QE,
      cut("3 * 0.33333333333333 = 1 ".asFormula)  <( eqL2R(-1)(2) & QE,
         QE)))

    pr shouldBe 'proved
  }


  "Partial QE" should "not fail on |-" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq(), IndexedSeq()), ToolTactics.partialQE(qeTool))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "false".asFormula
  }

  it should "turn x^2>=0 |- y>1 into |- y>1" in withMathematica { qeTool =>
    val result = proveBy(Sequent(IndexedSeq("x^2>=0".asFormula), IndexedSeq("y>1".asFormula)), ToolTactics.partialQE(qeTool))
    result.subgoals should have size 1
    result.subgoals.head.ante shouldBe empty
    result.subgoals.head.succ should contain only "y>1".asFormula
  }

}
