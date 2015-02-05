import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.{AxiomTactic, SyntacticDerivationAxiomTactics}
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{Tactic, PositionTactic}

/**
 * Created by nfulton on 2/5/15.
 */
class SyntacticDerivationTests extends TacticTestSuite {
  "AndDerivativeT tactics" should "atomize" in {
    val node = helper.formulaToNode(helper.parseFormula( " (1=1 & 2=2)' "))
    val tactic = helper.positionTacticToTactic(SyntacticDerivationAxiomTactics.AndDerivativeT)

    helper.runTactic(tactic, node, true)
    require(containsOpenGoal(node, helper.parseFormula("(1=1)' & (2=2)'")))
  }

  it should "agree on atomization" in {
    val node1 = helper.formulaToNode(helper.parseFormula( " (1=1 & 2=2)' "))
    val node2 = helper.formulaToNode(helper.parseFormula( " (1=1 & 2=2)' "))

    val tactic1 = helper.positionTacticToTactic(SyntacticDerivationAxiomTactics.AndDerivativeT)
    helper.runTactic(tactic1, node1, true)

    val tactic2 = helper.positionTacticToTactic(SyntacticDerivationAxiomTactics.AndDerivativeAtomizeT)
    helper.runTactic(tactic2, node2, true)

    require(node1.openGoals().length == node2.openGoals().length)
    require(containsOpenGoal(node1, helper.parseFormula("(1=1)' & (2=2)'")))
    require(containsOpenGoal(node2, helper.parseFormula("(1=1)' & (2=2)'")))
  }

  it should "also aggregation correctly and agreeably" in {
    val node1 = helper.formulaToNode(helper.parseFormula( " (1=1)' & (2=2)' "))
    val node2 = helper.formulaToNode(helper.parseFormula( " (1=1)' & (2=2)' "))

    val tactic1 = helper.positionTacticToTactic(SyntacticDerivationAxiomTactics.AndDerivativeT)
    helper.runTactic(tactic1, node1, true)

    val tactic2 = helper.positionTacticToTactic(SyntacticDerivationAxiomTactics.AndDerivativeAggregateT)
    helper.runTactic(tactic2, node2, true)

    require(node1.openGoals().length == node2.openGoals().length)
    require(containsOpenGoal(node1, helper.parseFormula(" (1=1 & 2=2)' ")))
    require(containsOpenGoal(node2, helper.parseFormula("(1=1 & 2=2)' ")))
  }

  "OrDerivativeT tactics" should "atomize" in {
    val node = helper.formulaToNode(helper.parseFormula( " (1=1 | 2=2)' "))
    val tactic = helper.positionTacticToTactic(SyntacticDerivationAxiomTactics.OrDerivativeT)

    helper.runTactic(tactic, node, true)
    require(containsOpenGoal(node, helper.parseFormula("(1=1)' | (2=2)'")))
  }

  it should "agree on atomization" in {
    val node1 = helper.formulaToNode(helper.parseFormula( " (1=1 | 2=2)' "))
    val node2 = helper.formulaToNode(helper.parseFormula( " (1=1 | 2=2)' "))

    val tactic1 = helper.positionTacticToTactic(SyntacticDerivationAxiomTactics.OrDerivativeT)
    helper.runTactic(tactic1, node1, true)

    val tactic2 = helper.positionTacticToTactic(SyntacticDerivationAxiomTactics.OrDerivativeAtomizeT)
    helper.runTactic(tactic2, node2, true)

    require(node1.openGoals().length == node2.openGoals().length)
    require(containsOpenGoal(node1, helper.parseFormula("(1=1)' | (2=2)'")))
    require(containsOpenGoal(node2, helper.parseFormula("(1=1)' | (2=2)'")))
  }

  it should "aggregate agreeably" in {
    val node1 = helper.formulaToNode(helper.parseFormula( " (1=1)' | (2=2)' "))
    val node2 = helper.formulaToNode(helper.parseFormula( " (1=1)' | (2=2)' "))

    val tactic1 = helper.positionTacticToTactic(SyntacticDerivationAxiomTactics.OrDerivativeT)
    helper.runTactic(tactic1, node1, true)

    val tactic2 = helper.positionTacticToTactic(SyntacticDerivationAxiomTactics.OrDerivativeAggregateT)
    helper.runTactic(tactic2, node2, true)

    require(node1.openGoals().length == node2.openGoals().length)
    require(containsOpenGoal(node1, helper.parseFormula("(1=1 | 2=2)'")))
    require(containsOpenGoal(node2, helper.parseFormula("(1=1 | 2=2)'")))
  }

  def testTermOperation(sNoParen : String, tNoParen : String, op : String, axTactic : AxiomTactic, atomizePosTactic : PositionTactic, aggregatePosTactic : PositionTactic) = {
    val s = "(" + sNoParen + ")"
    val t = "(" + tNoParen + ")"
    val tactic = helper.positionTacticToTactic(axTactic)
    val atomizeTactic = helper.positionTacticToTactic(atomizePosTactic)
    val aggregateTactic = helper.positionTacticToTactic(aggregatePosTactic)

    def primer(x:String) = "("+x+")'"

    val node = helper.formulaToNode(helper.parseFormula(
      primer(s + " " + op + " " + t)
    ))
    val node2 = helper.formulaToNode(helper.parseFormula(
      primer(s + " " + op + " " + t)
    ))
    helper.runTactic(tactic, node, true)
    helper.runTactic(atomizeTactic, node2, true)
    require(containsOpenGoal(node, helper.parseFormula(primer(s) + op + primer(t))))
    require(containsOpenGoal(node2, helper.parseFormula(primer(s) + op + primer(t))))


    //aggregation
    val node3 = helper.formulaToNode(helper.parseFormula(primer(s) + op + primer(t)))
    val node4 = helper.formulaToNode(helper.parseFormula(primer(s) + op + primer(t)))
    helper.runTactic(tactic, node3, true)
    helper.runTactic(aggregateTactic, node4, true)
    require(containsOpenGoal(node3, helper.parseFormula(primer(s + " " + op + " " + t))))
    require(containsOpenGoal(node4, helper.parseFormula(primer(s + " " + op + " " + t))))
  }

  import SyntacticDerivationAxiomTactics._

  "=" should "work on x,y" in {
    testTermOperation("x", "y", "=", EqualsDerivativeT, EqualsDerivativeAtomizeT, EqualsDerivativeAggregateT)
  }
  ">=" should "work on x,y" in {
    testTermOperation("x", "y", ">=", GreaterEqualDerivativeT, GreaterEqualDerivativeAtomizeT, GreaterEqualDerivativeAggregateT)
  }
  ">" should "work on x,y" in {
    testTermOperation("x", "y", ">", GreaterThanDerivativeT, GreaterThanDerivativeAtomizeT, GreaterThanDerivativeAggregateT)
  }
  "<=" should "work on x,y" in {
    testTermOperation("x", "y", "<=", LessEqualDerivativeT, LessEqualDerivativeAtomizeT, LessEqualDerivativeAggregateT)
  }
  "<" should "work on x,y" in {
    testTermOperation("x", "y", "<", LessThanDerivativeT, LessThanDerivativeAtomizeT, LessThanDerivativeAggregateT)
  }
  "!=" should "work on x,y" in {
    testTermOperation("x", "y", "!=", NotEqualsDerivativeT, NotEqualsDerivativeAtomizeT, NotEqualsDerivativeAggregateT)
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Syntactic derivation of terms
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


}
