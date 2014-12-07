import edu.cmu.cs.ls.keymaera.core.Mathematica
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{Matchers, FlatSpec}

/**
 * Created by nfulton on 12/6/14.
 */
class ProvabilityExamples extends FlatSpec with Matchers {
  val helper = new ProvabilityTestHelper()
  import helper._ // import helper methods for thests.

  "The Default Tactic" should "handle assignments" in {
    val problem1 = parseFormula("[x:=1;]x=1")
    tacticClosesProof(TacticLibrary.default, formulaToNode(problem1)) should be (true)
  }

  it should "timeout" in {
    val problem = parseFormula("1782^12 + 1841^12 != 1922^12")
    //hopefully this is false because things time out
    tacticFinishesAndClosesProof(1, TacticLibrary.default, formulaToNode(problem)) should be (false)
    //but if we want to be very sure the timeout causes the false result, we can make sure the result is None vs. Some(not closed):
    runTacticWithTimeout(1, TacticLibrary.default, formulaToNode(problem)) should be (None)
  }

}
