import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._


/**
 * Created by nfulton on 2/13/15.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class TermDerivationInContextTests extends TacticTestSuite {

  "subtract" should "replace" in {
    val orig = "[x':=1;](1-1)'=0".asFormula
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.SubtractDerivativeT)
    val node = helper.formulaToNode(orig)
    val result = helper.runTactic(tactic, node)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x':=1;]1'-1'=0".asFormula
  }

  it should "replace fvs" in {
    val orig = "[x':=1;](a-b)'=0".asFormula
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.SubtractDerivativeT)
    val node = helper.formulaToNode(orig)
    val result = helper.runTactic(tactic, node)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x':=1;](a)'-(b)'=0".asFormula
  }

  it should "replace bvs" in {
    val orig = "[x':=1;](x-b)'=0".asFormula
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.SubtractDerivativeT)
    val node = helper.formulaToNode(orig)
    val result = helper.runTactic(tactic, node)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x':=1;](x)'-(b)'=0".asFormula
  }

  it should "replace bvs in a larger expression." in {
    val orig = "[y' := 1;][x':=1;](x-b)'=0".asFormula
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.SubtractDerivativeT)
    val node = helper.formulaToNode(orig)
    val result = helper.runTactic(tactic, node)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[y' := 1;][x':=1;](x)'-(b)'=0".asFormula
  }

  "add" should "replace" in {
    val orig = "[x':=1;](1+1)'=0".asFormula
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.AddDerivativeT)
    val node = helper.formulaToNode(orig)
    val result = helper.runTactic(tactic, node, mustApply = true)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x':=1;]1'+1'=0".asFormula
  }

  it should "replace bvs" in {
    val orig = "[x':=1;](x+1)'=0".asFormula
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.AddDerivativeT)
    val node = helper.formulaToNode(orig)
    val result = helper.runTactic(tactic, node, mustApply = true)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x':=1;](x)'+1'=0".asFormula
  }

  "multiply" should "replace" in {
    val orig = "[x':=1;](a*b)'=0".asFormula
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.MultiplyDerivativeT)
    val node = helper.formulaToNode(orig)
    val result = helper.runTactic(tactic, node, mustApply = true)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x':=1;]((a)'*b + a*(b)')=0".asFormula
  }


  it should "replace bvs" in {
    val orig = "[x':=1;](x*b)'=0".asFormula
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.MultiplyDerivativeT)
    val node = helper.formulaToNode(orig)
    val result = helper.runTactic(tactic, node)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x':=1;]((x)'*b + x*(b)')=0".asFormula
  }

  "divide" should "replace" in {
    val orig = "[x':=1;](a/b)'=0".asFormula
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.DivideDerivativeT)
    val node = helper.formulaToNode(orig)
    val result = helper.runTactic(tactic, node)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x':=1;](((a)'*b - a*(b)') / b^2)=0".asFormula
  }

  it should "replace bvs" in {
    val orig = "[x':=1;](x/b)'=0".asFormula
    val tactic = SearchTacticsImpl.locateTerm(SyntacticDerivationInContext.DivideDerivativeT)
    val node = helper.formulaToNode(orig)
    val result = helper.runTactic(tactic, node)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x':=1;](((x)'*b - x*(b)') / b^2)=0".asFormula
  }

}
