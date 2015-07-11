import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.{SearchTacticsImpl, LogicalODESolver}
import org.scalatest.{PrivateMethodTester, FlatSpec, Matchers}
import testHelper.{ProvabilityTestHelper, StringConverter}
import StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary._

/**
 * @author Nathan Fulton
 * Created by nfulton on 4/23/15.
 */
class ODESolverTests extends TacticTestSuite with PrivateMethodTester {
  //Useful values used throughout these tests.
  val nov    = Variable("doesnotoccur", None, Real)
  val acc    = Variable("acc", None, Real) //oh wow Matchers has a publicly exposed variable named a...
  val v      = Variable("v", None, Real)
  val x      = Variable("x", None, Real)
  val xPrime = DifferentialSymbol(x)
  val t      = Variable("t", None, Real)
  val tPrime = DifferentialSymbol(t)
  val five   = Number(5)
  val two    = Number(2)
  val one    = Number(1)
  val zero   = Number(0)

  private def getOde(s : String) = s.asFormula.asInstanceOf[Box].program.asInstanceOf[DifferentialProgram]

  /**
   * @author Nathan Fulton
   */
  "Prove after time intro" should "work" in {
    val f = "x = 0 & v = 1 & a = 5 -> [{x' =v, v' = a}]x >= 0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = locateSucc(ImplyRightT) & LogicalODESolver.solveT(SuccPos(0))
    helper.runTactic(tactic, node)
    helper.report(node)
    node shouldBe 'closed
  }

  /**
   * @author Nathan Fulton
   */
  it should "work if there's already time in the ODE" in {
    val f = "x = 0 & v = 1 & a = 5 & t=0 -> [{x' =v, v' = a, t' = 0*t+1}]x >= 0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = locateSucc(ImplyRightT) & LogicalODESolver.solveT(SuccPos(0))
    helper.runTactic(tactic, node)
    helper.report(node)
    node shouldBe 'closed
  }

  /**
   * @author Nathan Fulton
   */
  it should "work if there's already a time in the ODE and it's not in explicit linear form" in {
    val f = "x = 0 & v = 1 & a = 5 & t=0 -> [{x' =v, v' = a, t' = 1}]x >= 0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = locateSucc(ImplyRightT) & LogicalODESolver.solveT(SuccPos(0))
    helper.runTactic(tactic, node)
    helper.report(node)
    node shouldBe 'closed
  }

  /**
   * @author Nathan Fulton
   */
  it should "work when we have two separate sets of linear vars." in {
    val f = "x = 0 & v = 1 & a = 5 & t=0 & w = 0 & z = 0 -> [{x' =v, v' = a, w' = z, t' = 1}]x >= 0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = locateSucc(ImplyRightT) & LogicalODESolver.solveT(SuccPos(0))
    helper.runTactic(tactic, node)
    helper.report(node)
    node shouldBe 'closed
  }

}
