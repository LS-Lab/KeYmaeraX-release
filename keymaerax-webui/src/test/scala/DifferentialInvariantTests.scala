import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tools.{KeYmaera, Mathematica}
import testHelper.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.StringConverter._

/**
 * A suite of fine-grained tests of the Differential Invariant tactics.
 * More integration-style tests are included in the DifferentialTests.scala style. These tests are more focused on testing
 * each subcompontent than for testing for e.g., overall soundness or utility.
 * Many of the formulas in these tests are absolute gibberish except that they have typical binding structures.
 * Created by nfulton on 1/13/15.
 */
class DifferentialInvariantTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Boilerplate
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  val helper = new ProvabilityTestHelper(x=>println(x))

  val mathematicaConfig = helper.mathematicaConfig

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.MathematicaScheduler.init(mathematicaConfig)
  }

  override def afterEach() = {
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler = null
    Tactics.MathematicaScheduler = null
  }

  private def containsOpenGoal(node:ProofNode, f:Formula) = node.openGoals().find(_.sequent.succ.contains(f)).nonEmpty


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Differential Assignment
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  "Differential Assignment" should "work" in {
    val f = "[x':=2;]x'>1".asFormula // should be parsed as differential symbols
    val expected = "2 > 1".asFormula

    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(HybridProgramTacticsImpl.boxDerivativeAssignT)
    val result = helper.runTactic(tactic, node, mustApply = true)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only expected
  }

  it should "work when there are differential symbols" in {
    val f = "[x':=2;]x'>1".asFormula
    val expected = "2 > 1".asFormula

    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(HybridProgramTacticsImpl.boxDerivativeAssignT)
    val result = helper.runTactic(tactic, node, mustApply = true)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only expected
  }

  ignore should "work in a more complicated example" in {
    val f = helper.parseFormula("[x' := a+2+2;](x' = x' & x' > y)")
    val expected = helper.parseFormula("a+2+2 = a+2+2 & a+2+2 > y")

    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(HybridProgramTacticsImpl.boxDerivativeAssignT)
    helper.runTactic(tactic, node, true)
    containsOpenGoal(node, expected) shouldBe (true)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff invariant system general
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //"General diff invariant" this is the second-to-last step
  ignore should "simple example." in {
    val f = helper.parseFormula("[x'=y, y'=x & x^2 + y^2 = 1;]x + y = 1")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantT)
    require(tactic.applicable(node))

    helper.runTactic(tactic,node)
    helper.report(node)
  }


}