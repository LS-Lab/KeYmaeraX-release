package LODESolverTests

import edu.cmu.cs.ls.keymaerax.core.SuccPos
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.{LogicalODESolver, ODETactics, TacticLibrary}

/**
 * These tests execute the Logical ODE Solver step-by-step on a number of examples.
 * Really useful for debugging when a particular step is broken.
 * Created by nfulton on 9/11/15.
 */
class LODESolverStepByStepTests extends testHelper.TacticTestSuite {
  //
  // Example 1
  //
  "Example 1" should "inverseDiffGhost -- non-system step" in {
    val formula = "(x=0&v=1&a=5&t=0) -> ([{v'=a,t'=0*t+1&t>=0&true}]5/2*t^2+1*t+0>=0)".asFormula
    val node = helper.formulaToNode(formula)

    val tactic = TacticLibrary.ImplyRightT(SuccPos(0)) & LogicalODESolver.successiveInverseDiffGhost(SuccPos(0))

    helper.runTactic(tactic, node)

    val openGoal = node.openGoals().head

    openGoal.sequent.ante.length shouldBe 1
    openGoal.sequent.succ.length shouldBe 1
    openGoal.sequent.ante.head shouldBe "(x=0&v=1&a=5&t=0)".asFormula
    openGoal.sequent.succ.head shouldBe "([{t'=0*t+1&t>=0&true}]5/2*t^2+1*t+0>=0)".asFormula
  }

  it should "not exeucte inverseDiffGhost when only time is primed" in {
    //w/ ante, prepend: (x=0&v=1&a=5&t=0) ->
    val formula = "([{t'=0*t+1&t>=0&true}]5/2*t^2+1*t+0>=0)".asFormula
    val node = helper.formulaToNode(formula)

    val tactic = LogicalODESolver.successiveInverseDiffGhost(SuccPos(0))

    tactic.applicable(node) shouldBe false
  }

  it should "apply diffSolveConstraintT when only time is left" in {
    val formula = "(x=0&v=1&a=5&t=0) -> ([{t'=0*t+1&t>=0&true}]5/2*t^2+1*t+0>=0)".asFormula
    val node = helper.formulaToNode(formula)

    val tactic = TacticLibrary.ImplyRightT(SuccPos(0)) & ODETactics.diffSolveConstraintT(SuccPos(0))

    helper.runTactic(tactic, node)
    fail("no test")
  }
}