package LODESolverTests

import testHelper.TacticTestSuite
import edu.cmu.cs.ls.keymaerax.core.SuccPos
import edu.cmu.cs.ls.keymaerax.tactics.ODETactics
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
 * These tests reproduce bugs (both current and historical) in the Logical ODE Solver
 * Created by nfulton on 9/11/15.
 */
class LODESolverBugs extends TacticTestSuite {
  /**
   * @note this was never a bug.
   */
  "diffSolveConstraintT" should "work for z' = 0" in {
    val formula = "[{z' = 1 & 2=2}]1=1".asFormula
    val node = helper.formulaToNode(formula)

    val tactic = ODETactics.diffSolveConstraintT(SuccPos(0))
    helper.runTactic(tactic, node)

    val s = helper.remainingSequent(node)

    s.ante.length shouldBe 0
    s.succ.length shouldBe 1
    s.succ.head shouldBe "\\forall T (T>=0->\\forall S (0<=S&S<=T->2=2)->[z:=z+1*T;]1=1)".asFormula
  }

  /**
   * @note causes a clash b/c z occurs on the RHS of z'.
   */
  it should "work for z' = 0*z + 1" in {
    val formula = "[{z' = 0*z+1 & 2=2}]1=1".asFormula
    val node = helper.formulaToNode(formula)

    val tactic = ODETactics.diffSolveConstraintT(SuccPos(0))
    helper.runTactic(tactic, node)

    val s = helper.remainingSequent(node)

    s.ante.length shouldBe 0
    s.succ.length shouldBe 1
    fail("no test")
  }
}