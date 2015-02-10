import edu.cmu.cs.ls.keymaera.tactics.SyntacticDerivationAxiomTactics._
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper

/**
 * These are post-development "integration" tests for syntactic derivation
 * Created by nfulton on 2/10/15.
 */
class SDTests extends TacticTestSuite {

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

    val expected = helper.parseFormula("[$$a'=b$$;](x'-y'<=0)")
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
}
