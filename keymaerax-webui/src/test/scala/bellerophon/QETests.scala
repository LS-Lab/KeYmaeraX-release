package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, BelleThrowable, SequentialInterpreter, SpoonFeedingInterpreter}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.launcher.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

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
    val result = proveBy(Sequent(IndexedSeq(), IndexedSeq()), ToolTactics.fullQE(qeTool))
    result.subgoals should have size 1
    result.subgoals.head shouldBe Sequent(IndexedSeq(), IndexedSeq(False))
  }

  it should "fail on parsed decimal representations" in withMathematica { qeTool =>
    val result = proveBy("0.33333333333333 = 1/3".asFormula,ToolTactics.fullQE(qeTool))
    result.isProved shouldBe false
    result.subgoals should have size 1
    result.subgoals.head.succ should contain theSameElementsAs "false".asFormula::Nil
  }

  it should "correct behavior (Z3)" in withZ3 { qeTool =>
    a [BelleThrowable] should be thrownBy proveBy("0.33333333333333 = 1/3".asFormula,ToolTactics.fullQE(qeTool))
  }

  it should "fail on internal decimal representations" in withMathematica { qeTool =>
    val result = proveBy(Equal(Number(0.33333333333333),Divide(Number(1),Number(3))),ToolTactics.fullQE(qeTool))
    result.isProved shouldBe false
    result.subgoals should have size 1
    result.subgoals.head.succ should contain theSameElementsAs "false".asFormula::Nil
  }

  it should "fail (?) on internal decimal representations (2)" in withMathematica { qeTool =>
    // This isn't as bad as the above two
    proveBy(Equal(Number(1.0),Minus(Number(4),Number(3))),ToolTactics.fullQE(qeTool)) shouldBe 'proved
  }

  it should "fail x()=x" in withMathematica { qeTool =>
    the [BelleThrowable] thrownBy proveBy("x()=x".asFormula, ToolTactics.fullQE(qeTool) & done) should have message
      """[Bellerophon Runtime] Expected proved provable, but got NoProofTermProvable(Provable(  ==>  x()=x
        |  from     ==>  false))""".stripMargin
  }

  it should "not choke on predicates" in withMathematica { tool =>
    proveBy("p_() & q_() -> 2<3".asFormula,ToolTactics.fullQE(tool)) shouldBe 'proved
  }

  it should "close predicates if possible" in withMathematica { tool =>
    proveBy("p_() & q_() -> p_() | 2<3".asFormula,ToolTactics.fullQE(tool)) shouldBe 'proved
  }

  it should "not fail when already proved" in withMathematica { tool =>
    proveBy("x>0 -> x>0".asFormula, prop & ToolTactics.fullQE(tool)) shouldBe 'proved
  }

  it should "not have soundness bug with decimal representations " in withMathematica { _ =>

    val pr = proveBy("false".asFormula,
      cut("1-3 * 0.33333333333333 = 0".asFormula) <( QE,
      cut("3 * 0.33333333333333 = 1 ".asFormula)  <( eqL2R(-1)(2) & QE,
         QE)))

    pr.isProved shouldBe false
    pr.subgoals should have size 1
    pr.subgoals.head.ante shouldBe empty
    pr.subgoals.head.succ should contain theSameElementsAs "false".asFormula::Nil
  }

  "QE with specific tool" should "succeed with Mathematica" in withMathematica { _ =>
    val tactic = TactixLibrary.QE(Nil, Some("Mathematica"))
    proveBy("x>0 -> x>=0".asFormula, tactic) shouldBe 'proved
  }

  it should "succeed with Z3" in withZ3 { _ =>
    val tactic = TactixLibrary.QE(Nil, Some("Z3"))
    proveBy("x>0 -> x>=0".asFormula, tactic) shouldBe 'proved
  }

  it should "fail on tool mismatch" in withMathematica { _ =>
    the [BelleThrowable] thrownBy proveBy("0=0".asFormula, TactixLibrary.QE(Nil, Some("Z3"))) should have message "[Bellerophon Runtime] QE requires Z3, but got None"
  }

  it should "switch between tools" in withDatabase { db =>
    val provider = new MathematicaZ3ToolProvider(DefaultConfiguration.currentMathematicaConfig)
    ToolProvider.setProvider(provider)
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>=0&\\exists s x*s^2>0 End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    interpreter(BelleParser("implyR(1); andR(1); <(QE({`Z3`}), QE({`Mathematica`}))"),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))
    db.extractTactic(proofId) shouldBe BelleParser("implyR(1); andR(1); <(QE({`Z3`}), QE({`Mathematica`}))")
    interpreter.kill()
  }

  it should "use the default tool" in withDatabase { db =>
    val provider = new MathematicaZ3ToolProvider(DefaultConfiguration.currentMathematicaConfig)
    ToolProvider.setProvider(provider)
    val modelContent = "Variables. R x. End. Problem. x>0 -> x>=0&x>=-1 End."
    val proofId = db.createProof(modelContent)
    val interpreter = registerInterpreter(SpoonFeedingInterpreter(proofId, -1, db.db.createProof, listener(db.db), SequentialInterpreter))
    interpreter(BelleParser("implyR(1); andR(1); <(QE, QE)"),
      BelleProvable(ProvableSig.startProof(KeYmaeraXProblemParser(modelContent))))
    db.extractTactic(proofId) shouldBe BelleParser("implyR(1); andR(1); <(QE, QE)")
  }

  it should "switch between tools from parsed tactic" in {
    val provider = new MathematicaZ3ToolProvider(DefaultConfiguration.currentMathematicaConfig)
    ToolProvider.setProvider(provider)
    val tactic = BelleParser("andR(1); <(QE({`Z3`}), andR(1) ; <(QE({`Mathematica`}), QE))")
    proveBy("x>0 ==> x>=0&\\exists s x*s^2>0&x>=-2".asSequent, tactic) shouldBe 'proved
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
