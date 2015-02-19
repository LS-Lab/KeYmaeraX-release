/**
 * Created by nfulton on 2/11/15.
 */

import edu.cmu.cs.ls.keymaera.core.{PosInExpr, SuccPosition}
import edu.cmu.cs.ls.keymaera.tactics.NNFRewrite._
import edu.cmu.cs.ls.keymaera.tactics.{TacticLibrary, PropositionalTacticsImpl, SearchTacticsImpl}

class NNFTests extends TacticTestSuite {
  "Double negation elimination" should "eliminate" in {
    val node = helper.formulaToNode(helper.parseFormula("!(!(1=1))"))
    val tactic = helper.positionTacticToTactic(ValidityOfDoubleNegationEliminationT)
    helper.runTactic(tactic, node, true)
    require(containsOnlyExactlyOpenGoal(node, helper.parseFormula("1=1")))
  }

  it should "place the new formula in the same location as the previous formula" in {
    val node = helper.formulaToNode(helper.parseFormula("!(!(1=1)) & 2=2"))
    val doubleNegationPosition = SuccPosition(0, PosInExpr(0 :: Nil))

    val tactic = ValidityOfDoubleNegationEliminationT(doubleNegationPosition)
    require(formulaAtExpr(node, doubleNegationPosition).get.equals(helper.parseFormula("!(!(1=1))")))
    helper.runTactic(tactic, node)
    println(formulaAtExpr(node, doubleNegationPosition).get)
    require(formulaAtExpr(node, doubleNegationPosition).get.equals(helper.parseFormula("(1=1)")))

    helper.report(node)
  }

  it should "work in context" in {
    val node = helper.formulaToNode(helper.parseFormula("[x:=1;](!(!(1=1)))"))
    val doubleNegationPosition = SuccPosition(0, PosInExpr(1 :: Nil))
    val tactic = DoubleNegationElimination(doubleNegationPosition)
    helper.runTactic(tactic,node,true)
    require(false) //@todo check this.
  }

  "demorgan &" should "have a working proof" in {

    val node = helper.formulaToNode(helper.parseFormula("(!(x=x & y=y)) <-> (!(x=x) | !(y=y))"))
    val pos = SuccPosition(0)
    val tactic = proofOfDeMorganConjunction(pos)
    helper.runTactic(tactic, node, true)
    node.isClosed() shouldBe true
  }

  it should "rewrite something" in {
    val node = helper.formulaToNode(helper.parseFormula("!(1=1 & 2=2) & 3=3"))
    val pos = SuccPosition(0, PosInExpr(0 :: Nil))

    val tactic = rewriteNegConjunct(pos)
    require(formulaAtExpr(node, pos).get.equals(helper.parseFormula("!(1=1 & 2=2)")))

    helper.runTactic(tactic, node)
    containsOpenGoal(node, helper.parseFormula("(!(1=1) | !(2=2)) & 3=3"))
    //@todo not sure how to test these...
  }

  "demorgan |" should "have a working proof" in {
    val node = helper.formulaToNode(helper.parseFormula("(!(x=x | y=y)) <-> (!(x=x) & !(y=y))"))
    val pos = SuccPosition(0)
    val tactic = proofOfDeMorganDisjunction(pos)
    helper.runTactic(tactic, node, true)
    node.isClosed() shouldBe true
  }

  it should "rewrite something" in {
    val node = helper.formulaToNode(helper.parseFormula("!(1=1 | 2=2) & 3=3"))
    val pos = SuccPosition(0, PosInExpr(0 :: Nil))

    val tactic = rewriteNegDisjunct(pos)
    require(formulaAtExpr(node, pos).get.equals(helper.parseFormula("!(1=1 | 2=2)")))

    helper.runTactic(tactic, node)
    containsOpenGoal(node, helper.parseFormula("(!(1=1) & !(2=2)) & 3=3"))
    //@todo not sure how to test these...
  }
}
