import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.{SearchTacticsImpl, LogicalODESolver}
import org.scalatest.{PrivateMethodTester, FlatSpec, Matchers}
import testHelper.{ProvabilityTestHelper, StringConverter}
import StringConverter._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._

/**
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

  "Prove after time intro" should "work" in {
    val f = "x = 0 & v = 1 & a = 5 -> [x' =v, v' = a;]x >= 0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = locateSucc(ImplyRightT) & LogicalODESolver.solveT(SuccPos(0))
    helper.runTactic(tactic, node)
    helper.report(node)
    node shouldBe 'closed
  }

}
