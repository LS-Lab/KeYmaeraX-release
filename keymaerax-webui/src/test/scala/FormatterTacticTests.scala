import edu.cmu.cs.ls.keymaerax.tactics.{Formatters, SearchTacticsImpl}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
 * Tests for formatting tactics.
 * Created by nfulton on 7/20/15.
 */
class FormatterTacticTests extends testHelper.TacticTestSuite {
  "And Canonizer" should "left-assoc a well-associated And." in {
    val f = "1=1 & 2=2 & 3=3".asFormula
    val node = helper.formulaToNode(f)
    val t = SearchTacticsImpl.locateSucc(Formatters.leftAssociateConj)
    t.applicable(node) shouldBe false
  }

  it should "check default assoc is left-assoc" in {
    "1=1 & 2=2 & 3=3".asFormula shouldBe "(1=1 & 2=2) & 3=3".asFormula
  }

  it should "left-associated an ill-associated And." in {
    val f = "1=1 & (2=2 & 3=3)".asFormula
    val node = helper.formulaToNode(f)
    val t = SearchTacticsImpl.locateSucc(Formatters.leftAssociateConj)
    helper.runTactic(t, node)
    node.openGoals().length shouldBe 1
    node.openGoals()(0).sequent.succ.length shouldBe 1
    node.openGoals()(0).sequent.succ(0) shouldBe "1=1 & 2=2 & 3=3".asFormula
  }

  it should "work in context" in {
    val f = "[x := 0;](1=1 & (2=2 & 3=3))".asFormula
    val node = helper.formulaToNode(f)
    val t = SearchTacticsImpl.locateSucc(
      SearchTacticsImpl.locateLargestSubformula(Formatters.leftAssociateConj))

    helper.runTactic(t, node)
    node.openGoals().length shouldBe 1
    node.openGoals()(0).sequent.succ.length shouldBe 1
    node.openGoals()(0).sequent.succ(0) shouldBe "[x := 0;]((1=1 & 2=2) & 3=3)".asFormula
    node.openGoals()(0).sequent.succ(0) shouldBe "[x := 0;](1=1 & 2=2 & 3=3)".asFormula
  }

  it should "work in binding context." in {
    val f = "[x := 0;](x=0 & (x!=2 & x!=3))".asFormula
    val node = helper.formulaToNode(f)
    val t = SearchTacticsImpl.locateSucc(
      SearchTacticsImpl.locateLargestSubformula(Formatters.leftAssociateConj))

    helper.runTactic(t, node)
    node.openGoals().length shouldBe 1
    node.openGoals()(0).sequent.succ.length shouldBe 1
    node.openGoals()(0).sequent.succ(0) shouldBe "[x := 0;](x=0 & x!=2 & x!=3)".asFormula
  }
}
