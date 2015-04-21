import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.core._
import testHelper.StringConverter._


/**
 * Created by nfulton on 2/13/15.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class TermDerivationInContextTests extends TacticTestSuite {

  "subtract" should "replace" in {
    val orig = helper.parseFormula("[x':=1;](1-1)'=0");
    val expected = helper.parseFormula("[x':=1;]1'-1'=0");
    val position = PosInExpr(1 :: 0 :: Nil)
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.SubtractDerivativeT)
    val node = helper.formulaToNode(orig)
    helper.runTactic(tactic, node)
    containsOnlyExactlyOpenGoal(node, expected) shouldBe true
  }

  it should "replace fvs" in {
    val orig = helper.parseFormula("[x':=1;](a-b)'=0");
    val expected = helper.parseFormula("[x':=1;]a'-b'=0");
    val position = PosInExpr(1 :: 0 :: Nil)
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.SubtractDerivativeT)
    val node = helper.formulaToNode(orig)
    helper.runTactic(tactic, node)
    containsOnlyExactlyOpenGoal(node, expected) shouldBe true
  }

  it should "replace bvs" in {
    val orig = helper.parseFormula("[x':=1;](x-b)'=0");
    val expected = helper.parseFormula("[x':=1;]x'-b'=0");
    val position = PosInExpr(1 :: 0 :: Nil)
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.SubtractDerivativeT)
    val node = helper.formulaToNode(orig)
    helper.runTactic(tactic, node)
    containsOnlyExactlyOpenGoal(node, expected) shouldBe true
  }

  it should "replace bvs in a larger expression." in {
    val orig = helper.parseFormula("[y' := 1;][x':=1;](x-b)'=0");
    val expected = helper.parseFormula("[y' := 1;][x':=1;]x'-b'=0");
    val position = PosInExpr(1 :: 0 :: Nil)
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.SubtractDerivativeT)
    val node = helper.formulaToNode(orig)
    helper.runTactic(tactic, node)
    containsOnlyExactlyOpenGoal(node, expected) shouldBe true
  }

  "add" should "replace" in {
    val orig = helper.parseFormula("[x':=1;](1+1)'=0");
    val expected = helper.parseFormula("[x':=1;]1'+1'=0");
    val position = PosInExpr(1 :: 0 :: Nil)
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.AddDerivativeT)
    val node = helper.formulaToNode(orig)
    helper.runTactic(tactic, node, true)
    containsOnlyExactlyOpenGoal(node, expected) shouldBe true
  }

  it should "replace bvs" in {
    val orig = helper.parseFormula("[x':=1;](x+1)'=0");
    val expected = helper.parseFormula("[x':=1;]x'+1'=0");
    val position = PosInExpr(1 :: 0 :: Nil)
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.AddDerivativeT)
    val node = helper.formulaToNode(orig)
    helper.runTactic(tactic, node, true)
    containsOnlyExactlyOpenGoal(node, expected) shouldBe true
  }

  "multiply" should "replace" in {
    val orig = helper.parseFormula("[x':=1;](a*b)'=0");
    val expected = helper.parseFormula("[x':=1;](a'*b + a*b')=0");
    val position = PosInExpr(1 :: 0 :: Nil)
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.MultiplyDerivativeT)
    val node = helper.formulaToNode(orig)
    helper.runTactic(tactic, node)
    containsOnlyExactlyOpenGoal(node, expected) shouldBe true
  }


  it should "replace bvs" in {
    val orig = helper.parseFormula("[x':=1;](x*b)'=0");
    val expected = helper.parseFormula("[x':=1;](x'*b + x*b')=0");
    val position = PosInExpr(1 :: 0 :: Nil)
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.MultiplyDerivativeT)
    val node = helper.formulaToNode(orig)
    helper.runTactic(tactic, node)
    containsOnlyExactlyOpenGoal(node, expected) shouldBe true
  }

  "divide" should "replace" in {
    val orig = helper.parseFormula("[x':=1;](a/b)'=0");
    val expected = helper.parseFormula("[x':=1;]((a'*b - a*b') / b^2)=0");
    val position = PosInExpr(1 :: 0 :: Nil)
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.DivideDerivativeT)
    val node = helper.formulaToNode(orig)
    helper.runTactic(tactic, node)
    containsOnlyExactlyOpenGoal(node, expected) shouldBe true
  }

  it should "replace bvs" in {
    val orig = helper.parseFormula("[x':=1;](x/b)'=0");
    val expected = helper.parseFormula("[x':=1;]((x'*b - x*b') / b^2)=0");
    val position = PosInExpr(1 :: 0 :: Nil)
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.DivideDerivativeT)
    val node = helper.formulaToNode(orig)
    helper.runTactic(tactic, node)
    containsOnlyExactlyOpenGoal(node, expected) shouldBe true
  }

}
