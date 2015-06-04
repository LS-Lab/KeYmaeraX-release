import edu.cmu.cs.ls.keymaerax.tactics.{PosInExpr, RootNode, SuccPosition, SearchTacticsImpl}
import edu.cmu.cs.ls.keymaerax.tactics.SyntacticDerivationInContext._
import testHelper.StringConverter._
import testHelper.SequentFactory._

import scala.language.postfixOps

/**
 * These are post-development "integration" tests for syntactic derivation
 * Created by nfulton on 2/10/15.
 */
class SDTests extends TacticTestSuite {
  "Subtraction derivation" should "work without context" in {
    val in = "((x)'+(y)') = 0".asFormula
    val out = "(x+y)' = 0".asFormula

    val node = helper.formulaToNode(out)
    val tactic = AddDerivativeT(SuccPosition(0, PosInExpr(0 :: Nil)))
    helper.runTactic(tactic, node, mustApply = true)

    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only in
  }

  it should "work after non-binding assignment" in {
    val in = "[a':=0;]((x)'+(y)') = 0".asFormula
    val out = "[a':=0;](x+y)' = 0".asFormula

    val node = helper.formulaToNode(out)
    val tactic = SearchTacticsImpl.locateTerm(AddDerivativeT)
    helper.runTactic(tactic, node, mustApply = true)

    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only in
  }

  "Syntactic Derivation" should "work when there's no binding" in {
    val node = helper.formulaToNode("[a'=b;](x-y<1)'".asFormula)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    val result = helper.runTactic(tactic, node, mustApply = true)

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[a'=b & true;]x'-y'<=0".asFormula
  }

  it should "work on an identical example with assignment" in {
    //@todo the fact that SyntacticDerivationT finds its own position at which to apply is arguably a bug -- witness inf looping (findApplicablePositionForTermAxiom)
    val node = helper.formulaToNode("[a:=b;](x-y<1)'".asFormula)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    val result = helper.runTactic(tactic, node, mustApply = true)

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[a:=b;]x'-y'<=0".asFormula
  }

  it should "work when the next step is syntactic term derivation context" in {
    val node = helper.formulaToNode("[x':=b;](x-y)'<=1'".asFormula)

    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationT)
    val result = helper.runTactic(tactic, node, mustApply = true)

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x':=b;]x'-y'<=0".asFormula
  }

  it should "work on formulas containing bound variables." in {
    val node = helper.formulaToNode("[x'=b;](x+y<1)'".asFormula)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    val result = helper.runTactic(tactic, node, mustApply = true)

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x'=b;]x'+y'<=0".asFormula
  }

  it should "work on an identical example when there is binding inside of a marked box" in {
    val node = helper.formulaToNode("[x'=b;](x-y<1)'".asFormula)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    val result = helper.runTactic(tactic, node, mustApply = true)

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x'=b;]x'-y'<=0".asFormula
  }

  it should "identical to prev test but alpha-varied" in {
    val node = helper.formulaToNode("[a'=b;](a-y<1)'".asFormula)

    val tactic = helper.positionTacticToTactic(SyntacticDerivationT)
    val result = helper.runTactic(tactic, node, mustApply = true)

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[a'=b;]a'-y'<=0".asFormula
  }

  "Syntactic derivation of constant function symbols" should "work" in {
    val tactic = SearchTacticsImpl.locateSucc(SyntacticDerivationT)
    val s = sucSequent("c()'<=5".asFormula)
    val node = helper.runTactic(tactic, new RootNode(s), mustApply = true)
    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "0<=5".asFormula
  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Non-integration tests of the K-modal approach to in-context term derivations.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  "ImplyDerivative" should "work in a context" in {
    val node = helper.formulaToNode("[x:=1;](x=1 -> 2=2)'".asFormula)
    val tactic = ImplyDerivativeT(SuccPosition(0, PosInExpr(1::Nil)))
    val result = helper.runTactic(tactic, node)

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x:=1;]((!(x=1) | 2=2)')".asFormula
  }

  it should "work in a nested context" in {
    val node = helper.formulaToNode("[x':=1;][y':=1;](x=1 -> y=2)'".asFormula) //nonsense
    val tactic = ImplyDerivativeT(SuccPosition(0, PosInExpr(1::1::Nil)))
    val result = helper.runTactic(tactic, node)

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x':=1;][y':=1;]((!(x=1) | y=2)')".asFormula
  }

  "LessThanDerivativeT" should "work in a nested context" in {
    val node = helper.formulaToNode("[x':=1;][y':=1;](x < y)'".asFormula) //nonsense
    val tactic = LessThanDerivativeT(SuccPosition(0, PosInExpr(1::1::Nil)))
    val result = helper.runTactic(tactic, node)

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x':=1;][y':=1;]((x)' <= (y)')".asFormula
  }

  "monomial derivation" should "work outside of context" in {
    val node = helper.formulaToNode("(x^2)'=0".asFormula)
    val tactic = SearchTacticsImpl.locateTerm(PowerDerivativeT)
    val result = helper.runTactic(tactic, node)

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "2*x^(2-1)*(x)'=0".asFormula
  }

  it should "work inside of a non-binding context" in {
    val node = helper.formulaToNode("[a := 0;](x^2)'=0".asFormula)
    val tactic = SearchTacticsImpl.locateTerm(PowerDerivativeT)
    val result = helper.runTactic(tactic, node)

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[a := 0;]2*x^(2-1)*(x)'=0".asFormula
  }

  it should "work inside of a binding context" in {
    val node = helper.formulaToNode("[x := 0;](x^2)'=0".asFormula)
    val tactic = SearchTacticsImpl.locateTerm(PowerDerivativeT)
    val result = helper.runTactic(tactic, node)

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x := 0;]2*x^(2-1)*(x)'=0".asFormula
  }

  "constant derivation" should "work" in {
    val f = "[x := 0;] (2)'=0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = SearchTacticsImpl.locateTerm(ConstantDerivativeT)
    val result = helper.runTactic(tactic, node)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x := 0;] 0=0".asFormula
  }

  "Failure scenarios from dsolve" should "be fixed for the failure case from x'=v,v'=a (using multiplyderivative)" in {
    val f= "x'=(0*2-1*0)/2^2*(a*kxtime_1^2+2*kxtime_1*v_2+2*x_2)+1/2*(a'*kxtime_1^2+a*(2*kxtime_1^1)+((2*kxtime_1)'*v_2+2*kxtime_1*v_2')+(2*x_2)')".asFormula
    val n = helper.formulaToNode(f)
    val result = helper.runTactic(SearchTacticsImpl.locateTerm(MultiplyDerivativeT)*, n, mustApply = true)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x'=(0*2-1*0)/2^2*(a*kxtime_1^2+2*kxtime_1*v_2+2*x_2)+1/2*(a'*kxtime_1^2+a*(2*kxtime_1^1)+((2'*kxtime_1+2*(kxtime_1)')*v_2+2*kxtime_1*v_2')+(2'*x_2+2*(x_2)'))".asFormula
  }

  it should "be fixed for the failure case from x'=v,v'=a (using bare sytnacticderivationt)" in {
    val f= "x'=(0*2-1*0)/2^2*(a*kxtime_1^2+2*kxtime_1*v_2+2*x_2)+1/2*(a'*kxtime_1^2+a*(2*kxtime_1^1)+((2*kxtime_1)'*v_2+2*kxtime_1*v_2')+(2*x_2)')".asFormula
    val expected = "x'=(0*2-1*0)/2^2*(a*kxtime_1^2+2*kxtime_1*v_2+2*x_2)+1/2*(a'*kxtime_1^2+a*(2*kxtime_1^1)+((0*kxtime_1+2*kxtime_1')*v_2+2*kxtime_1*v_2')+(0*x_2+2*x_2'))".asFormula
    val n = helper.formulaToNode(f)
    val result = helper.runTactic(SearchTacticsImpl.locateTerm(SyntacticDerivationT)*, n, mustApply = true)
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only expected
  }


  it should "be fixed for Tues. night example 2" in {
    val f = "x'=(1'*2-1*2')/2^2*(a*kxtime_1^2+2*kxtime_1*v_2+2*x_2)+1/2*(a*kxtime_1^2+2*kxtime_1*v_2+2*x_2)'".asFormula
    val n = helper.formulaToNode(f)

    helper.runTactic(SearchTacticsImpl.locateTerm(SyntacticDerivationT)*, n, mustApply = true)

  }
}
