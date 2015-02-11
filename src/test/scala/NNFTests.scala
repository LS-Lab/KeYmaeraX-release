/**
 * Created by nfulton on 2/11/15.
 */

import edu.cmu.cs.ls.keymaera.core.{PosInExpr, SuccPosition}
import edu.cmu.cs.ls.keymaera.tactics.NNFRewrite._

class NNFTests extends TacticTestSuite {
  "Double negation elimination" should "eliminate" in {
    val node = helper.formulaToNode(helper.parseFormula("!(!(1=1))"))
    val tactic = helper.positionTacticToTactic(DoubleNegationEliminationT)
    helper.runTactic(tactic, node, true)
    require(containsOnlyExactlyOpenGoal(node, helper.parseFormula("1=1")))
  }

  it should "place the new formula in the same location as the previous formula" in {
    val node = helper.formulaToNode(helper.parseFormula("!(!(1=1)) & 2=2"))
    val doubleNegationPosition = SuccPosition(0, PosInExpr(0 :: Nil))

    val tactic = DoubleNegationEliminationT(doubleNegationPosition)
    require(formulaAtExpr(node, doubleNegationPosition).get.equals(helper.parseFormula("!(!(1=1))")))

  }
}
