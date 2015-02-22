import edu.cmu.cs.ls.keymaera.core.{SuccPosition, PosInExpr}
import edu.cmu.cs.ls.keymaera.tactics.SyntacticDerivationAxiomTactics._
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper

/**
 * These are post-development "integration" tests for syntactic derivation
 * Created by nfulton on 2/10/15.
 */
class SDTests extends TacticTestSuite {

  "Subtraction derivation" should "work" in {
    val in = helper.parseFormula(" (x'+y') = 0")
    val out = helper.parseFormula(" (x+y)' = 0")

    val node = helper.formulaToNode(out)
    val tactic = AddDerivativeT(SuccPosition(0, PosInExpr(0 :: Nil)))
    helper.runTactic(tactic,node, true)
    containsOpenGoal(node, in) shouldBe(true)
  }

  "Syntactic Derivation" should "work when there's no binding" in {
    val f = helper.parseFormula("[a'=b;](x-y<1)'")
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    helper.runTactic(tactic, node, true)

    val expected = helper.parseFormula("[a'=b;](x'-y'<=0)")
    helper.report(node)
    require(containsOpenGoal(node, expected))
  }

  it should "work on marked boxes when there's no binding" in {
    val f = helper.parseFormula("[$$a'=b$$;](x-y<1)'")
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    helper.runTactic(tactic, node, true)

    val expected = helper.parseFormula("[$$a'=b$$;](x'-y'<=1')")
    helper.report(node)
    require(containsOpenGoal(node, expected))
  }

  it should "work on an identical example when there is binding assignment" in {
    val f = helper.parseFormula("[x:=b;](x-y<1)'")
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    helper.runTactic(tactic, node, true)

    val expected = helper.parseFormula("[x:=b;](x'-y'<=1')")
    helper.report(node)
    require(containsOpenGoal(node, expected))
  }

  it should "work on an identical example when there is binding" in {
    val f = helper.parseFormula("[x'=b;](x-y<1)'")
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    helper.runTactic(tactic, node, true)

    val expected = helper.parseFormula("[x'=b;](x'-y'<=0)")
    helper.report(node)
    require(containsOpenGoal(node, expected))
  }

  it should "work on an identical example when there is binding inside of a marked box" in {
    val f = helper.parseFormula("[x'=b;](x-y<1)'")
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    helper.runTactic(tactic, node, true)

    val expected = helper.parseFormula("[$$x'=b$$;](x'-y'<=0)")
    helper.report(node)
    require(containsOpenGoal(node, expected))
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // These are all tests which apply to the new approach which allows the use of these axioms in context. I'm not sure
  // if the old tests will still pass, or if they should.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  "ImplyDerivative" should "work in no context" in {
    val f = helper.parseFormula(" (1=1 -> 2=2)' ")
    val expected = helper.parseFormula(" (!(1=1) | 2=2)' ")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ImplyDerivativeT)
    helper.runTactic(tactic, node)
    helper.report(node)
    require(containsOpenGoal(node, expected))
  }

  it should "work in a context" in {
    val f = helper.parseFormula("[x:=1;](x=1 -> 2=2)'")
    val expected = helper.parseFormula("[x:=1;]((!(x=1) | 2=2)')")
    val node = helper.formulaToNode(f)
    val tactic = ImplyDerivativeT(SuccPosition(0, PosInExpr(1::Nil)))
    helper.runTactic(tactic, node)
    helper.report(node)
    require(containsOpenGoal(node, expected))
  }

  it should "work in a nested context" in {
    val f = helper.parseFormula("[x':=1;][y':=1;](x=1 -> y=2)'") //non-sense.
    val expected = helper.parseFormula("[x':=1;][y':=1;]((!(x=1) | y=2)')")
    val node = helper.formulaToNode(f)
    val tactic = ImplyDerivativeT(SuccPosition(0, PosInExpr(1::1::Nil)))
    helper.runTactic(tactic, node)
    helper.report(node)
    require(containsOpenGoal(node, expected))
  }

  "LessThanDerivativeT" should "work in a nested context" in {
    val f = helper.parseFormula("[x':=1;][y':=1;](x < y)'") //non-sense.
    val expected = helper.parseFormula("[x':=1;][y':=1;](x' <= y')")
    val node = helper.formulaToNode(f)
    val tactic = LessThanDerivativeT(SuccPosition(0, PosInExpr(1::1::Nil)))
    helper.runTactic(tactic, node)
    helper.report(node)
    require(containsOpenGoal(node, expected))
  }


  // Diagnosing diverging SubtractDerivativeT tactic.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  "SubtractDerivativeT" should "see how we're doing w/ subtraction" in {
    val f = helper.parseFormula("(1-1)' = 0")
    val expected = helper.parseFormula("1' - 1' = 0")
    val node = helper.formulaToNode(f)
    val tactic = SubtractDerivativeT(SuccPosition(0, PosInExpr(0 :: Nil)))
    helper.runTactic(tactic, node)
    helper.report(node)
  }

  it should "converge when there is no binding context" in {
    val f = helper.parseFormula("[x':=0;] (a-1)' = 0")
    val node = helper.formulaToNode(f)
    val tactic = SubtractDerivativeT(SuccPosition(0, PosInExpr(1 :: 0 :: Nil)))
    helper.runTactic(tactic, node)
    helper.report(node)
  }

  it should "work when there is binding context" in { //@todo this test is currently diverging because term tactics do not work in context.
    val f = helper.parseFormula("[a':=0;] (a-1)' = 0")
    val expected = helper.parseFormula("1' - 1' = 0")
    val node = helper.formulaToNode(f)
    val tactic = (SubtractDerivativeT(SuccPosition(0, PosInExpr(1 :: 0 :: Nil))) *) //Will diverge if the tactic doesn't work.
    helper.runTactic(tactic, node)
    helper.report(node)
  }
}
