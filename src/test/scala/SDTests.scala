import edu.cmu.cs.ls.keymaera.core.{Sequent, SuccPosition, PosInExpr}
import edu.cmu.cs.ls.keymaera.tactics.{SyntacticDerivativeTermAxiomsInContext, SearchTacticsImpl}
import edu.cmu.cs.ls.keymaera.tactics.SyntacticDerivationInContext._
import testHelper.StringConverter._

/**
 * These are post-development "integration" tests for syntactic derivation
 * Created by nfulton on 2/10/15.
 */
class SDTests extends TacticTestSuite {
  "Subtraction derivation" should "work without context" in {
    val in = "(x'+y') = 0".asFormula
    val out = "(x+y)' = 0".asFormula

    val node = helper.formulaToNode(out)
    val tactic = AddDerivativeT(SuccPosition(0, PosInExpr(0 :: Nil)))
    helper.runTactic(tactic, node, mustApply = true)

    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only in
  }

  it should "work after non-binding assignment" in {
    val in = "[a':=0;](x'+y') = 0".asFormula
    val out = "[a':=0;](x+y)' = 0".asFormula

    val node = helper.formulaToNode(out)
    val tactic = SearchTacticsImpl.locateTerm(AddDerivativeT)
    helper.runTactic(tactic, node, mustApply = true)

    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only in
  }

  "Syntactic Derivation" should "work when there's no binding" in {
    val f = helper.parseFormula("[a'=b;](x-y<1)'")
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    helper.runTactic(tactic, node, true)

    val expected = helper.parseFormula("[a'=b & true;](x'-y'<=1')")
    helper.report(node)
    containsOpenGoal(node, expected) shouldBe true
  }

  it should "work on marked boxes when there's no binding" in {
    val f = helper.parseFormula("[$$a'=b$$;](x-y<1)'")  //@todo the fact that SyntacticDerivationT finds its own position at which to apply is arguably a bug -- witness inf looping
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    helper.runTactic(tactic, node, true)

    val expected = helper.parseFormula("[$$a'=b$$;](x'-y'<=1')")
    helper.report(node)
    containsOpenGoal(node, expected) shouldBe true
  }

  it should "work on an identical example with assignment" in {
    val f = helper.parseFormula("[a:=b;](x-y<1)'") //@todo the fact that SyntacticDerivationT finds its own position at which to apply is arguably a bug -- witness inf looping (findApplicablePositionForTermAxiom)
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    helper.runTactic(tactic, node, true)

    val expected = helper.parseFormula("[a:=b;](x'-y'<=1')")
    helper.report(node)
    containsOpenGoal(node, expected) shouldBe true
  }

  it should "work when the next step is syntactic term derivation context" in {
    val f = helper.parseFormula("[x':=b;](x-y)'<=1'")
    val node = helper.formulaToNode(f)

    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationT)
    helper.runTactic(tactic, node, true)

    val expected = helper.parseFormula("[x':=b;](x'-y'<=1')")
    helper.report(node)
    containsOpenGoal(node, expected) shouldBe true
  }

  it should "work on formulas containing bound variables." in {
    val f = helper.parseFormula("[x'=b;](x+y<1)'")
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    helper.runTactic(tactic, node, true)

    val expected = helper.parseFormula("[x'=b;](x'+y'<=1')")
    helper.report(node)
    containsOpenGoal(node, expected) shouldBe true
  }

  it should "work on an identical example when there is binding inside of a marked box" in {
    val f = helper.parseFormula("[x'=b;](x-y<1)'")
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    helper.runTactic(tactic, node, true)

    val expected = helper.parseFormula("[x'=b;](x'-y'<=1')")
    helper.report(node)
    require(containsOpenGoal(node, expected))
  }

  it should "identical to prev test but alpha-varied" in {
    val f = helper.parseFormula("[a'=b;](a-y<1)'")
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    helper.runTactic(tactic, node, true)

    val expected = helper.parseFormula("[a'=b;](a'-y'<=1')")
    helper.report(node)
    require(containsOpenGoal(node, expected))
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Non-integration tests of the K-modal approach to in-context term derivations.
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
}
