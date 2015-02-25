import edu.cmu.cs.ls.keymaera.core.{DeriveMonomial, Sequent, SuccPosition, PosInExpr}
import edu.cmu.cs.ls.keymaera.tactics.{SyntacticDerivativeProofRulesInContext, SyntacticDerivativeTermAxiomsInContext, SearchTacticsImpl}
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

  "monomial derivation" should "work outside of context" in {
    val f = helper.parseFormula("(x^2)'=0")
    val node = helper.formulaToNode(f)
    val tactic = SearchTacticsImpl.locateTerm(MonomialDerivativeT)
    helper.runTactic(tactic, node)
    helper.report(node)
    containsOpenGoal(node, helper.parseFormula("2*x^1=0")) shouldBe true
    node.openGoals().length shouldBe 1
  }

  it should "work inside of a non-binding context" in {
    val f = helper.parseFormula("[a := 0;](x^2)'=0")
    val node = helper.formulaToNode(f)
    val tactic = SearchTacticsImpl.locateTerm(MonomialDerivativeT)
    helper.runTactic(tactic, node)
    containsOpenGoal(node, helper.parseFormula("[a := 0;]2*x^1=0")) shouldBe true
    node.openGoals().length shouldBe 1
  }

  it should "work inside of a binding context" in {
    val f = helper.parseFormula("[x := 0;](x^2)'=0")
    val node = helper.formulaToNode(f)
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivativeProofRulesInContext.MonomialDerivativeInContext)
    helper.runTactic(tactic, node)
    containsOpenGoal(node, helper.parseFormula("[x := 0;]2*x^1=0")) shouldBe true
    node.openGoals().length shouldBe 1


  }

  "constant derivation" should "work" in {
    val f = helper.parseFormula("[x := 0;] (2)'=0")
    val node = helper.formulaToNode(f)
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivativeProofRulesInContext.ConstantDerivativeInContext)
    helper.runTactic(tactic, node)
    containsOpenGoal(node, helper.parseFormula("[x := 0;]0=0")) shouldBe true
    node.openGoals().length shouldBe 1
  }

  "Failure scenarios from dsolve" should "be fixed for the failure case from x'=v,v'=a (using multiplyderivative)" in {
    val f= "x'=(0*2-1*0)/2^2*(a*k4_t_1^2+2*k4_t_1*v_2+2*x_2)+1/2*(a'*k4_t_1^2+a*(2*k4_t_1^1)+((2*k4_t_1)'*v_2+2*k4_t_1*v_2')+(2*x_2)')".asFormula
    val expected = helper.parseFormula("x'=(0*2-1*0)/2^2*(a*k4_t_1^2+2*k4_t_1*v_2+2*x_2)+1/2*(a'*k4_t_1^2+a*(2*k4_t_1^1)+((2'*k4_t_1+2*k4_t_1')*v_2+2*k4_t_1*v_2')+(2'*x_2+2*x_2'))")
    val n = helper.formulaToNode(f)
    helper.runTactic((SearchTacticsImpl.locateTerm(MultiplyDerivativeT)*), n, true)
    containsOpenGoal(n, expected) shouldBe true
  }

  it should "be fixed for the failure case from x'=v,v'=a (using bare sytnacticderivationt)" in {
    val f= "x'=(0*2-1*0)/2^2*(a*k4_t_1^2+2*k4_t_1*v_2+2*x_2)+1/2*(a'*k4_t_1^2+a*(2*k4_t_1^1)+((2*k4_t_1)'*v_2+2*k4_t_1*v_2')+(2*x_2)')".asFormula
    val expected = helper.parseFormula("x'=(0*2-1*0)/2^2*(a*k4_t_1^2+2*k4_t_1*v_2+2*x_2)+1/2*(a'*k4_t_1^2+a*(2*k4_t_1^1)+((2'*k4_t_1+2*k4_t_1')*v_2+2*k4_t_1*v_2')+(2'*x_2+2*x_2'))")
    val n = helper.formulaToNode(f)
    helper.runTactic((SearchTacticsImpl.locateTerm(SyntacticDerivationT)*), n, true)
    containsOpenGoal(n, expected) shouldBe (true)
  }
}
