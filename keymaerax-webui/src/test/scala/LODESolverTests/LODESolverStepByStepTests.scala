package LODESolverTests

import edu.cmu.cs.ls.keymaerax.core.{Equiv, Forall, SuccPos}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics._

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

  it should "apply diffSolveConstraintT when only time is left -- no alpha-renaming necessary" in {
    val formula = "(x=0&v=1&a=5&t=0) -> ([{z'=0*z+1&z>=0&true}]5/2*z^2+1*z+0>=0)".asFormula
    val node = helper.formulaToNode(formula)

    val tactic = TacticLibrary.ImplyRightT(SuccPos(0)) & SearchTacticsImpl.locateTerm(ODETactics.rewriteConstantTime) ~ ODETactics.diffSolveConstraintT(SuccPos(0))

    helper.runTactic(tactic, node)
    //Of the bureaucracy below should be fixed whenevber rewriteContantTime is working again, and then
    //actualReaminingGoal will be the only open goal.
    node.openGoals().length shouldBe 2
    val actualRemainingGoal = {
      //Find the goal that's suspposed to actually be there...
      val firstGoal = node.openGoals().head
      val secondGoal = node.openGoals().last
      val (actualRemainingGoal: ProofNode, rewriteConstantTimeGoal: ProofNode) =
        (firstGoal.sequent.succ.head) match {
          case Forall(_, _) => (firstGoal, secondGoal)
          case _ => (secondGoal, firstGoal)
        }
      actualRemainingGoal
    }

    actualRemainingGoal.sequent.succ.head shouldBe "\\forall T (T>=0->\\forall S (0<=S&S<=T->z+1*S>=0&true)->[z:=z+1*T;]5/2*z^2+1*z+0>=0)".asFormula
  }

  it should "apply diffSolveConstraintT when only time is left" in {
    val formula = "(x=0&v=1&a=5&t=0) -> ([{t'=0*t+1&t>=0&true}]5/2*t^2+1*t+0>=0)".asFormula
    val node = helper.formulaToNode(formula)

    val tactic = TacticLibrary.ImplyRightT(SuccPos(0)) & SearchTacticsImpl.locateTerm(ODETactics.rewriteConstantTime) ~ ODETactics.diffSolveConstraintT(SuccPos(0))

    helper.runTactic(tactic, node)
    //Of the bureaucracy below should be fixed whenevber rewriteContantTime is working again, and then
    //actualReaminingGoal will be the only open goal.
    node.openGoals().length shouldBe 2
    val actualRemainingGoal = {
      //Find the goal that's suspposed to actually be there...
      val firstGoal = node.openGoals().head
      val secondGoal = node.openGoals().last
      val (actualRemainingGoal: ProofNode, rewriteConstantTimeGoal: ProofNode) =
        (firstGoal.sequent.succ.head) match {
          case Forall(_, _) => (firstGoal, secondGoal)
          case _ => (secondGoal, firstGoal)
        }
      actualRemainingGoal
    }
    actualRemainingGoal.sequent.succ.head shouldBe "\\forall T (T>=0->\\forall S (0<=S&S<=T->z+1*S>=0&true)->[t:=t+1*T;]5/2*t^2+1*t+0>=0)".asFormula
  }

  it should "close after DS& is finished" in {
    val f = "x=0&v=1&a=5&t=0 -> \\forall T (T>=0->\\forall S (0<=S&S<=T->z+1*S>=0&true)->[z:=z+1*T;]5/2*z^2+1*z+0>=0)".asFormula
    val node = helper.formulaToNode(f)

    val tactic = TacticLibrary.ImplyRightT(SuccPos(0)) & LogicalODESolver.reduceToArithmetic(SuccPos(0))

    helper.runTactic(tactic, node)
    node shouldBe 'closed
  }
}