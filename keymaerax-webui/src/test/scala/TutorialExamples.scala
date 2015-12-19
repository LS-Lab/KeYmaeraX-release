import edu.cmu.cs.ls.keymaerax.btactics.FOQuantifierTactics
import edu.cmu.cs.ls.keymaerax.core.SuccPos
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary._

/**
  * Created by nfulton on 12/15/15.
  */
class TutorialExamples extends testHelper.TacticTestSuite {
  /**
    * @author Nathan Fulton
    */
  "Weak Logical ODE Solver" should "work when time is explicit" in {
    val f = "x = 0 & v = 1 & a = 5 & t=0 -> [{x' =v, v' = a, t' = 1}]x >= 0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = locateSucc(ImplyRightT) & LogicalODESolver.weakSolveT(SuccPos(0))
    helper.runTactic(tactic, node)
    helper.report(node)
    node shouldBe 'closed
  }

  /**
    * @author Nathan Fulton
    */
  "Logical ODE Solver" should "work when time is explicit" in {
    val f = "x = 0 & v = 1 & a = 5 & t=0 -> [{x' =v, v' = a, t' = 1}]x >= 0".asFormula
    val node = helper.formulaToNode(f)
    val tactic =
      locateSucc(ImplyRightT) &
      LogicalODESolver.solveT(SuccPos(0)) &
      locateSucc(FOQuantifierTacticsImpl.skolemizeT) & locateSucc(ImplyRightT) &
      locateSucc(ImplyRightT) &
      locateSucc(HybridProgramTacticsImpl.boxAssignT) &
      TacticLibrary.arithmeticT

    helper.runTactic(tactic, node)
    helper.report(node)
    node shouldBe 'closed
  }
}
