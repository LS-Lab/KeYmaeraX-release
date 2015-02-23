import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.{HybridProgramTacticsImpl, ODETactics}
import testHelper.StringConverter._

/**
 * Created by nfulton on 2/22/15.
 */
class DiffInvIntegrationTests extends TacticTestSuite {

  "Assign" should "work" in {
    val f = "[a := 0;]a = 0".asFormula
    val node = helper.formulaToNode(f)
    helper.runTactic(helper.positionTacticToTactic(HybridProgramTacticsImpl.boxAssignT), node)
    helper.report(node)
  }

  "Diff Assign" should "work with 1 box" in {
    val f = "[a' := 1;]a'=1".asFormula
    val node = helper.formulaToNode(f)
    helper.runTactic(helper.positionTacticToTactic(HybridProgramTacticsImpl.boxDerivativeAssignT), node)
  }

  it should "work with 1 box and an unprimed occurance" in {
    val f = "[a' := 1;](a=1 -> a'=1)".asFormula
    val node = helper.formulaToNode(f)
    helper.runTactic(helper.positionTacticToTactic(HybridProgramTacticsImpl.boxDerivativeAssignT), node)
  }

  it should "work with 2 boxes" in {
    val f = "[a' := 1;](a>b -> [b' := 1;](true -> a'=b))'".asFormula
    val node = helper.formulaToNode(f)
    helper.runTactic((helper.positionTacticToTactic(HybridProgramTacticsImpl.boxDerivativeAssignT) *), node)
  }



  def runDiffInv(f : Formula) = {
    val node = helper.formulaToNode(f)
    helper.runTactic(helper.positionTacticToTactic(ODETactics.diffInvariantT), node)
    helper.report(node)
    node
  }


  "diff inv tactic" should "work" in {
    val f = "[x' = y, y' = x & x^2 + y^2 = 4;]1=1".asFormula
    val n = runDiffInv(f)
  }
}
