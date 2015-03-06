import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
 * A suite of fine-grained tests of the Differential Invariant tactics.
 * More integration-style tests are included in the DifferentialTests.scala style. These tests are more focused on testing
 * each subcompontent than for testing for e.g., overall soundness or utility.
 * Many of the formulas in these tests are absolute gibberish except that they have typical binding structures.
 * Created by nfulton on 1/13/15.
 */
class DifferentialInvariantTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Boilerplate
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  val helper = new ProvabilityTestHelper(x=>println(x))

  val mathematicaConfig = helper.mathematicaConfig

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.MathematicaScheduler.init(mathematicaConfig)
  }

  override def afterEach() = {
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler = null
    Tactics.MathematicaScheduler = null
  }

  private def containsOpenGoal(node:ProofNode, f:Formula) =
    !node.openGoals().find(_.sequent.succ.contains(f)).isEmpty


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Differential Assignment
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  "Differential Assignment" should "work" in {
    val f = helper.parseFormula("[x' := 2;]x' > 1")
    val expected = helper.parseFormula("2 > 1")

    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(HybridProgramTacticsImpl.boxDerivativeAssignT)
    helper.runTactic(tactic, node, true)
    containsOpenGoal(node, expected) shouldBe (true)
  }

  ignore should "work in a more complicated example" in {
    val f = helper.parseFormula("[x' := a+2+2;](x' = x' & x' > y)")
    val expected = helper.parseFormula("a+2+2 = a+2+2 & a+2+2 > y")

    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(HybridProgramTacticsImpl.boxDerivativeAssignT)
    helper.runTactic(tactic, node, true)
    containsOpenGoal(node, expected) shouldBe (true)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Differential invariants where invariant is already part of the formula? @todo
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //"The axiom-based differential invariant tactic"
  ignore should "work when there IS a test condition (no tests when there is none..." in {
    val f = helper.parseFormula("[x'=1 & true;]z>=0")
    f match {
      case BoxModality(ContEvolveProduct(_: NFContEvolve,_), _) => ()
      case _ => fail("parsed into wrong form.")
    }
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantNormalFormT)

    helper.runTactic(tactic,node)
    helper.report(node)
    val expected = helper.parseFormula("[x'=1 & true;](true->[(x'):=1;](z>=0)')")
    require(containsOpenGoal(node,expected))
  }


  it should "simplest example with a test" in {
    val f = helper.parseFormula("[x'=1 & z>0;]z>=0")
    f match {
      case BoxModality(ContEvolveProduct(_: NFContEvolve, _), _) => ()
      case BoxModality(pi,phi) => fail("f doesn't match the applicability condition; wanted an NFContEvolve but got a: " + pi)
      case _ => fail("Expected a modality but got something completely wrong.")
    }

    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantNormalFormT)

    tactic.applicable(node) should be (true)
    try {
      helper.runTactic(tactic, node)
    }
    catch {
      case e: Exception => fail("Expected no exceptions.")
    }

    val expectedResult = helper.parseFormula("[x'=1 & (z>0);](z>0->[(x'):=1;](z>=0)')")

    require(node.openGoals().map(pn => {
      val f = pn.sequent.succ.last
      f == expectedResult
    }).contains(true))
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff invariant system introduction'
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  "DI System Marker Intro" should "introduce a marker when there is a test" in {
    val f=  helper.parseFormula("[x'=y, y'=x & 1=1;]1=1")
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemIntroT)
    assert(tactic.applicable(node))
    helper.runTactic(tactic, node)

    //@todo the introduction of true here is strange behavior, but I think intended. We should document this carefully.
    val expected = helper.parseFormula("1=1&[$$x'=y & true,y'=x & (1=1)$$;](1=1)'")
    require(containsOpenGoal(node, expected))
  }

  it should "introduce a marker when there is no test" in {
    val f=  helper.parseFormula("[x'=y, y'=x;]1=1")
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemIntroT)
    assert(tactic.applicable(node))
    helper.runTactic(tactic, node)

    //@todo the introduction of true here is strange behavior, but I think intended. We should document this carefully.
    val expected = helper.parseFormula("1=1&[$$x'=y & true,y'=x$$;](1=1)'")
    containsOpenGoal(node, expected) shouldBe true
  }

  it should "introduce a marker when there are interleaved tests" in {
    val f=  helper.parseFormula("[x'=y & 2=2, y'=x & 3=3;]1=1")
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemIntroT)
    assert(tactic.applicable(node))
    helper.runTactic(tactic, node)

    val expected = helper.parseFormula("1=1&[$$x'=y & 2=2,y'=x & 3=3$$;](1=1)'")
    containsOpenGoal(node, expected) shouldBe true
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff invariant system head test
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  "Diff invariant system head test" should "peel off 1st equation" in {
    val f = helper.parseFormula("[$$ x'=y & 2=2, y'=x & 3=3$$;]1=1")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemHeadT)
    require(tactic.applicable(node))

    helper.runTactic(tactic, node)

    val expected = helper.parseFormula("[$$y'=x & (3=3),x' ≚ y & (2=2)$$;][(x'):=y;](2=2->1=1)")
    containsOpenGoal(node,expected) shouldBe(true)
  }

  it should "peel off 2nd equation" in {
    val f = helper.parseFormula("[$$y'=x & 3=3,x' ≚ y & 2=2$$;][(x'):=y;]1=1")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemHeadT)
    require(tactic.applicable(node))

    helper.runTactic(tactic, node)

    val expected = helper.parseFormula("[$$x' ≚ y & (2=2),y' ≚ x & (3=3)$$;][(y'):=x;](3=3->[(x'):=y;]1=1)")
    containsOpenGoal(node,expected) shouldBe (true)
  }

  it should "peel off 1st equation -- no xs" in {
    val f = helper.parseFormula("[$$ a'=y & 2=2, y'=a & 3=3$$;]1=1")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemHeadT)
    require(tactic.applicable(node))

    helper.runTactic(tactic, node)

    val expected = helper.parseFormula("[$$y'=a & (3=3),a'≚y & (2=2)$$;][(a'):=y;](2=2->1=1)")
    containsOpenGoal(node,expected) shouldBe true
  }

  it should "peel off 2nd equation -- no xs" in {
    val f = helper.parseFormula("[$$y'=a & (3=3),a'≚y & (2=2)$$;][(a'):=y;](2=2->1=1)")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemHeadT)
    require(tactic.applicable(node))

    helper.runTactic(tactic, node)

    val expected = helper.parseFormula("[$$a'≚y & (2=2),y'≚a & (3=3)$$;][(y'):=a;](3=3->[(a'):=y;](2=2->1=1))")
    containsOpenGoal(node,expected) shouldBe true
  }

  it should "not apply in a variety of conditions" in {
    val f = helper.parseFormula("[$$x'≚y & true,y'≚x & true$$;][(y'):=x;][(x'):=y;]1=1")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemHeadT)
    require(!tactic.applicable(node))
  }
//
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff invariant system tail
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  "Diff invariant system tail" should "apply to an appropriate system" in {
    val f = helper.parseFormula("[$$a'≚y & (2=2),y'≚a & (3=3)$$;][(y'):=a;](3=3->[(a'):=y;]1=1)")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemTailT)
    require(tactic.applicable(node))
    helper.runTactic(tactic, node)
    require(containsOpenGoal(node, helper.parseFormula("[(y'):=a;](3=3->[(a'):=y;]1=1)")))
  }

  it should "not apply to an inappropriate system" in {
    val expected = helper.parseFormula("[$$a'=y & (2=2),y'≚a & (3=3)$$;][(y'):=a;](3=3->[(a'):=y;]1=1)") //just removed the ` from the first equality.
    val node = helper.formulaToNode(expected)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemTailT)
    require(!tactic.applicable(node))
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff invariant system general
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //"General diff invariant" this is the second-to-last step
  ignore should "simple example." in {
    val f = helper.parseFormula("[x'=y, y'=x & x^2 + y^2 = 1;]x + y = 1")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantT)
    require(tactic.applicable(node))

    helper.runTactic(tactic,node)
    helper.report(node)
  }


}