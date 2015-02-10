import edu.cmu.cs.ls.keymaera.core.ExpressionTraversal.TraverseToPosition
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.{TacticLibrary, TermAxiomTactic, AxiomTactic, SyntacticDerivationAxiomTactics}
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
    require(containsOpenGoal(node, helper.parseFormula("(1=1)' & (2=2)'")))
  }

  it should "agree on atomization" in {
    val node1 = helper.formulaToNode(helper.parseFormula( " (1=1 | 2=2)' "))
    val node2 = helper.formulaToNode(helper.parseFormula( " (1=1 | 2=2)' "))

    val tactic1 = helper.positionTacticToTactic(SyntacticDerivationAxiomTactics.OrDerivativeT)
    helper.runTactic(tactic1, node1, true)

    val tactic2 = helper.positionTacticToTactic(SyntacticDerivationAxiomTactics.OrDerivativeAtomizeT)
    helper.runTactic(tactic2, node2, true)

    require(node1.openGoals().length == node2.openGoals().length)
    require(containsOpenGoal(node1, helper.parseFormula("(1=1)' & (2=2)'")))
    require(containsOpenGoal(node2, helper.parseFormula("(1=1)' & (2=2)'")))
  }

  it should "aggregate agreeably" in {
    val node1 = helper.formulaToNode(helper.parseFormula( " (1=1)' & (2=2)' "))
    val node2 = helper.formulaToNode(helper.parseFormula( " (1=1)' & (2=2)' "))

    val tactic1 = helper.positionTacticToTactic(SyntacticDerivationAxiomTactics.OrDerivativeT)
    helper.runTactic(tactic1, node1, true)

    val tactic2 = helper.positionTacticToTactic(SyntacticDerivationAxiomTactics.OrDerivativeAggregateT)
    helper.runTactic(tactic2, node2, true)

    require(node1.openGoals().length == node2.openGoals().length)
    require(containsOpenGoal(node1, helper.parseFormula("(1=1 | 2=2)'")))
    require(containsOpenGoal(node2, helper.parseFormula("(1=1 | 2=2)'")))
  }

  def testTermOperation(sNoParen : String, tNoParen : String, innerOp : String, outerOp: String, axTactic : AxiomTactic, atomizePosTactic : PositionTactic, aggregatePosTactic : PositionTactic) = {
    val s = "(" + sNoParen + ")"
    val t = "(" + tNoParen + ")"
    val tactic = helper.positionTacticToTactic(axTactic)
    val atomizeTactic = helper.positionTacticToTactic(atomizePosTactic)
    val aggregateTactic = helper.positionTacticToTactic(aggregatePosTactic)

    def primer(x:String) = "("+x+")'"

    val node = helper.formulaToNode(helper.parseFormula(
      primer(s + " " + innerOp + " " + t)
    ))
    val node2 = helper.formulaToNode(helper.parseFormula(
      primer(s + " " + innerOp + " " + t)
    ))
    helper.runTactic(tactic, node, true)
    helper.runTactic(atomizeTactic, node2, true)
    require(containsOpenGoal(node, helper.parseFormula(primer(s) + outerOp + primer(t))))
    require(containsOpenGoal(node2, helper.parseFormula(primer(s) + outerOp + primer(t))))


    //aggregation
    val node3 = helper.formulaToNode(helper.parseFormula(primer(s) + outerOp + primer(t)))
    val node4 = helper.formulaToNode(helper.parseFormula(primer(s) + outerOp + primer(t)))
    helper.runTactic(tactic, node3, true)
    helper.runTactic(aggregateTactic, node4, true)
    require(containsOpenGoal(node3, helper.parseFormula(primer(s + " " + innerOp + " " + t))))
    require(containsOpenGoal(node4, helper.parseFormula(primer(s + " " + innerOp + " " + t))))
  }

  import SyntacticDerivationAxiomTactics._

  "=" should "work on x,y" in {
    testTermOperation("x", "y", "=", "=", EqualsDerivativeT, EqualsDerivativeAtomizeT, EqualsDerivativeAggregateT)
  }
  ">=" should "work on x,y" in {
    testTermOperation("x", "y", ">=",">=", GreaterEqualDerivativeT, GreaterEqualDerivativeAtomizeT, GreaterEqualDerivativeAggregateT)
  }
  "<=" should "work on x,y" in {
    testTermOperation("x", "y", "<=","<=", LessEqualDerivativeT, LessEqualDerivativeAtomizeT, LessEqualDerivativeAggregateT)
  }

  //These axioms don't follow the above pattern, so we need something slightly modified.

  ">" should "work on x,y" in {
    testTermOperation("x", "y", ">",">=", GreaterThanDerivativeT, GreaterThanDerivativeAtomizeT, GreaterThanDerivativeAggregateT)
  }
  "<" should "work on x,y" in {
    testTermOperation("x", "y", "<", "<=", LessThanDerivativeT, LessThanDerivativeAtomizeT, LessThanDerivativeAggregateT)
  }
  "!=" should "work on x,y" in {
    testTermOperation("x", "y", "!=", "=", NotEqualsDerivativeT, NotEqualsDerivativeAtomizeT, NotEqualsDerivativeAggregateT)
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Syntactic derivation of terms
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  "syntactic derivation of negation" should "work on x,y" in {
    val outerFormula = helper.parseFormula(" (-(x+x))' = 0")
    val innerFormula = helper.parseFormula(" -((x+x)') = 0")

    val node = helper.formulaToNode(outerFormula)
    val tactic = NegativeDerivativeT(SuccPosition(0, PosInExpr(0 :: Nil)))
    helper.runTactic(tactic,node, true)
    require(containsOpenGoal(node, innerFormula))

    //@todo not currently testing the other direction because we'll need more infrastructure to support equality being applied in the "other" direction.
    //@todo uncommenting one line of the applies method in the NegaativeDerivativeT implementation is enough to make these commented-out lines pass.
//    val node2 = helper.formulaToNode(innerFormula)
//    helper.runTactic(tactic,node2)
//    require(containsOpenGoal(node2, outerFormula))
  }

  def innerOuterTest(innerFormula:Formula, outerFormula:Formula, axTactic:TermAxiomTactic) = {
    //first one direction.
    val node = helper.formulaToNode(outerFormula)
    val tactic = axTactic(SuccPosition(0, PosInExpr(0 :: Nil)))
    helper.runTactic(tactic,node, true)
    require(containsOpenGoal(node, innerFormula))

    //Then the other direction as well. @todo We need term position tactics before this can be enabled again.
//    val node2 = helper.formulaToNode(innerFormula)
//    helper.runTactic(tactic, node, true)
//    require(containsOpenGoal(node, innerFormula))
  }

  "syntactic derivation of addition" should "work on x,y" in {
    val in = helper.parseFormula(" (x'+y') = 0")
    val out = helper.parseFormula(" (x+y)' = 0")
    innerOuterTest(in,out,AddDerivativeT)
  }

  "syntactic derivation of subtraction" should "work on x,y" in {
    val in = helper.parseFormula(" (x'-y') = 0")
    val out = helper.parseFormula(" (x-y)' = 0")
    innerOuterTest(in,out,SubtractDerivativeT)
  }

  "syntactic derivation of multiplication" should "work on x,y" in {
    val in = helper.parseFormula(" ((x')*y) + (x*(y')) = 0")
    val out = helper.parseFormula(" (x*y)' = 0")
    innerOuterTest(in,out,MultiplyDerivativeT)
  }

  "syntactic derivation of division" should "work on x,y" in {
    val in = helper.parseFormula("(((x')*y) - (x*(y'))) / (y^2) = 0")
    val out = helper.parseFormula("(x / y)' = 0")
    innerOuterTest(in,out,DivideDerivativeT)

  }

  "TermSyntacticDerivationT" should "work for +" in {
    val in = helper.parseFormula("n*m + (a+b)' + 1 + c^n = a^2 + 2") //nonsense idk just want some extra terms.
    val node = helper.formulaToNode(in)
    val tactic = TermSyntacticDerivationT(SuccPosition(0, PosInExpr(0 :: Nil)))
    helper.runTactic(tactic,node)
    require(containsOpenGoal(node, helper.parseFormula("n*m + (a'+b') + 1 + c^n = a^2 + 2"))) //again, nonsense...
  }

  it should "work for -y" in {
    val in = helper.parseFormula("n*m + (-y)' + 1 + c^n = a^2 + 2") //nonsense idk just want some extra terms.
    val node = helper.formulaToNode(in)
    val tactic = TermSyntacticDerivationT(SuccPosition(0, PosInExpr(0 :: Nil)))
    helper.runTactic(tactic,node)
    require(containsOpenGoal(node, helper.parseFormula("n*m + -(y') + 1 + c^n = a^2 + 2"))) //again, nonsense...
  }

  it should "work for -x" in {
    val in = helper.parseFormula("n*m + (-x)' + 1 + c^n = a^2 + 2") //nonsense idk just want some extra terms.
    val node = helper.formulaToNode(in)
    val tactic = TermSyntacticDerivationT(SuccPosition(0, PosInExpr(0 :: Nil)))
    helper.runTactic(tactic,node)
    require(containsOpenGoal(node, helper.parseFormula("n*m + -(x') + 1 + c^n = a^2 + 2"))) //again, nonsense...
  }

  "FormulaSyntacticDerivationT" should "work for |" in {
    val f = helper.parseFormula("(1'=1 | 2=2)'")
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(FormulaSyntacticDerivationT)
    helper.runTactic(tactic, node, true)

    val expected = helper.parseFormula("(1'=1)'&(2=2)'")
    helper.report(node)
    require(containsOpenGoal(node, expected))
  }

  it should "work for =" in {
    val f = helper.parseFormula("(1 = 2)'")
    val node = helper.formulaToNode(f)
    val ptactic = TacticLibrary.ClosureT(FormulaSyntacticDerivationT)

    val tactic = helper.positionTacticToTactic(ptactic)
    helper.runTactic(tactic, node, true)
    val expected = helper.parseFormula("1' = 2'")
    require(containsOpenGoal(node, expected))
  }

  "SyntacticDerivationT" should "intermediate step for next test" in {
    val f = helper.parseFormula("(1=1)' & true")
    val node = helper.formulaToNode(f)

    val position = SuccPosition(0, PosInExpr(List(0)))
    val tactic = EqualsDerivativeT(position)

    helper.runTactic(tactic, node, true)

    val expected = helper.parseFormula("(1'=1') & true")
    helper.report(node)
    require(containsOpenGoal(node, expected))
  }

  it should "work for | with an internal term that needs rewriting" in {
    val f = helper.parseFormula("(1'=1 | 2=2)'")
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    helper.runTactic(tactic, node, true)

    val expected = helper.parseFormula("((1')'=1')&(2'=2')")
    helper.report(node)
    require(containsOpenGoal(node, expected))
  }
}
