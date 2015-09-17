/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.{Tactic, PositionTactic}
import edu.cmu.cs.ls.keymaerax.tactics.{PosInExpr, SearchTacticsImpl, SuccPosition, TacticLibrary, NNFRewrite}
import edu.cmu.cs.ls.keymaerax.tactics.NNFRewrite._
import testHelper.KeYmaeraXTestTags

/**
 * Created by nfulton on 2/11/15.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class NNFTests extends testHelper.TacticTestSuite {
  "Double negation elimination" should "eliminate" in {
    val node = helper.formulaToNode("!(!(1=1))".asFormula)
    val tactic = helper.positionTacticToTactic(rewriteDoubleNegationEliminationT)
    helper.runTactic(tactic, node, mustApply = true)
    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "1=1".asFormula
  }

  it should "place the new formula in the same location as the previous formula" in {
    val node = helper.formulaToNode("!(!(1=1)) & 2=2".asFormula)
    val doubleNegationPosition = SuccPosition(0, PosInExpr(0 :: Nil))

    val tactic = rewriteDoubleNegationEliminationT(doubleNegationPosition)

    formulaAtExpr(node, doubleNegationPosition).get should be ("!(!(1=1))".asFormula)
    helper.runTactic(tactic, node)
    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "1=1&2=2".asFormula
  }

  it should "work in subformulas" in {
    val node = helper.formulaToNode("[x:=1;](!(!(1=1)))".asFormula)
    val doubleNegationPosition = SuccPosition(0, PosInExpr(1 :: Nil))
    val tactic = rewriteDoubleNegationEliminationT(doubleNegationPosition)
    helper.runTactic(tactic, node, mustApply = true)
    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "[x:=1;]1=1".asFormula
  }

  "demorgan &" should "have a working proof" in {
    val node = helper.formulaToNode(helper.parseFormula("(!(x=x & y=y)) <-> (!(x=x) | !(y=y))"))
    val pos = SuccPosition(0)
    val tactic = proofOfDeMorganConjunction(pos)
    helper.runTactic(tactic, node, mustApply = true) shouldBe 'closed
  }

  it should "rewrite something" in {
    val node = helper.formulaToNode(helper.parseFormula("!(1=1 & 2=2) & 3=3"))
    val pos = SuccPosition(0, PosInExpr(0 :: Nil))

    val tactic = rewriteNegConjunct(pos)

    helper.runTactic(tactic, node)
    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "(!1=1 | !2=2) & 3=3".asFormula
  }

  "demorgan |" should "have a working proof" in {
    val node = helper.formulaToNode("(!(x=x | y=y)) <-> (!(x=x) & !(y=y))".asFormula)
    val pos = SuccPosition(0)
    val tactic = proofOfDeMorganDisjunction(pos)
    helper.runTactic(tactic, node, mustApply = true) shouldBe 'closed
  }

  it should "rewrite something" in {
    val node = helper.formulaToNode("!(1=1 | 2=2) & 3=3".asFormula)
    val pos = SuccPosition(0, PosInExpr(0 :: Nil))

    val tactic = rewriteNegDisjunct(pos)

    helper.runTactic(tactic, node)
    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "(!1=1 & !2=2) & 3=3".asFormula
  }


  "implication to disjunction" should "work" in {
    val node = helper.formulaToNode("1=1 -> 2=2".asFormula)
    val tactic = rewriteImplicationToDisjunction(SuccPosition(0))
    helper.runTactic(tactic, node)
    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "(!1=1 | 2=2)".asFormula
  }

  "the entire rewrite" should "work" in {
    val node = helper.formulaToNode("!( (1=1 | 2=2) & !(!(2=2)) )".asFormula)
    val tactic = NNFRewrite(SuccPosition(0))

    helper.runTactic(tactic, node)
    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "( 1!=1 & 2!=2 ) | 2!=2".asFormula //OK.
  }

  it should "prove example 1" taggedAs(KeYmaeraXTestTags.SummaryTest) in {
    import TacticLibrary.{EquivRightT,AxiomCloseT}
    import scala.language.postfixOps

    val node = helper.formulaToNode("((2=2&3=3)->4=4)<->(!(2=2&3=3)|4=4)".asFormula)
    val pos = SuccPosition(0)

    def l : PositionTactic => Tactic = SearchTacticsImpl.locateSubposition(pos)
    val nnfTactics =
      (l(rewriteImplicationToDisjunction) | l(rewriteNegConjunct) |
        l(rewriteNegDisjunct) | l(rewriteDoubleNegationEliminationT))*

    val tactic = nnfTactics ~ (EquivRightT(pos) & AxiomCloseT)
    helper.runTactic(tactic, node, mustApply = true) shouldBe 'closed
  }

  it should "work 2" taggedAs(KeYmaeraXTestTags.SummaryTest) in {
    val node = helper.formulaToNode("!( (1=1 | 2=2) -> !(!(2=2)) )".asFormula)
    val tactic = NNFRewrite(SuccPosition(0))

    helper.runTactic(tactic, node)
    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "(1=1|2=2) & 2!=2".asFormula //OK.
  }
}
