import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.StringConverter._

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

  private def containsOpenGoal(node:ProofNode, f:Formula) = node.openGoals().find(_.sequent.succ.contains(f)).nonEmpty


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Differential Assignment
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  "Differential Assignment" should "work" in {
    val f = helper.parseFormula("[x' := 2;]x' > 1")
    val expected = helper.parseFormula("2 > 1")

    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(HybridProgramTacticsImpl.boxDerivativeAssignT)
    helper.runTactic(tactic, node, mustApply = true)
    containsOpenGoal(node, expected) shouldBe true
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
//  ignore should "work when there IS a test condition (no tests when there is none..." in {
//    val f = helper.parseFormula("[x'=1 & true;]z>=0")
//    f match {
//      case BoxModality(ODESystem(_, _, _), _) => ()
//      case _ => fail("parsed into wrong form.")
//    }
//    val node = helper.formulaToNode(f)
//    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantNormalFormT)
//
//    helper.runTactic(tactic,node)
//    helper.report(node)
//    val expected = helper.parseFormula("[x'=1 & true;](true->[(x'):=1;](z>=0)')")
//    require(containsOpenGoal(node,expected))
//  }
//
//
//  ignore should "simplest example with a test" in {
//    val f = "[x'=1 & z>0;]z>=0".asFormula
//    val node = helper.formulaToNode(f)
//    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantNormalFormT)
//
//    tactic.applicable(node) shouldBe true
//    val result = helper.runTactic(tactic, node)
//    result.openGoals() should have size 1
//    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
//    result.openGoals().flatMap(_.sequent.succ) should contain only "(z>0 -> z>=0) & [x'=1 & z>0;][(x'):=1;](z>=0)'".asFormula
//  }
//
//  // TODO alpha renaming not yet correct
//  ignore should "alpha rename in simplest example with a test" in {
//    val f = "[y'=1 & z>0;]z>=0".asFormula
//    val node = helper.formulaToNode(f)
//    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantNormalFormT)
//
//    tactic.applicable(node) shouldBe true
//    val result = helper.runTactic(tactic, node)
//    result.openGoals() should have size 1
//    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
//    result.openGoals().flatMap(_.sequent.succ) should contain only "(z>0 -> z>=0) & [y'=1 & z>0;][(y'):=1;](z>=0)'".asFormula
//  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff invariant system introduction'
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  "DI System Marker Intro" should "introduce a marker when there is a test" in {
    val f =  "[x'=y, y'=x & 1=1;]1=1".asFormula
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemIntroT)
    tactic.applicable(node) shouldBe true
    val result = helper.runTactic(tactic, node)

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "1=1 -> (1=1&[$$x'=y, y'=x$$ & (1=1);](1=1)')".asFormula
  }

  it should "introduce a marker when there is no test" in {
    val f =  "[x'=y, y'=x;]1=1".asFormula
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemIntroT)
    tactic.applicable(node) shouldBe true
    val result = helper.runTactic(tactic, node)

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "true -> (1=1&[$$x'=y,y'=x$$;](1=1)')".asFormula
  }

  // TODO not yet supported by parser
  ignore should "introduce a marker when there are interleaved tests" in {
    val f=  helper.parseFormula("[x'=y & 2=2, y'=x & 3=3;]1=1")
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemIntroT)
    assert(tactic.applicable(node))
    helper.runTactic(tactic, node)

    val expected = helper.parseFormula("(2=2 & 3=3 -> 1=1)&[$$x'=y,y'=x$$ & 2=2 & 3=3;](1=1)'")
    containsOpenGoal(node, expected) shouldBe true
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff invariant system head test
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  "Diff invariant system head test" should "peel off 1st equation" in {
    val f = helper.parseFormula("[$$ x'=y, y'=x$$ & 2=2 & 3=3;]1=1")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemHeadT)
    require(tactic.applicable(node))

    helper.runTactic(tactic, node)

    val expected = helper.parseFormula("[$$y'=x,x' ≚ y$$ & 2=2 & 3=3;][(x'):=y;]1=1")
    containsOpenGoal(node,expected) shouldBe true
  }

  it should "peel off 2nd equation" in {
    val f = helper.parseFormula("[$$y'=x,x' ≚ y$$ & 2=2 & 3=3;][(x'):=y;]1=1")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemHeadT)
    require(tactic.applicable(node))

    helper.runTactic(tactic, node)

    val expected = helper.parseFormula("[$$x' ≚ y,y' ≚ x$$ & 2=2 & 3=3;][(y'):=x;][(x'):=y;]1=1")
    containsOpenGoal(node,expected) shouldBe true
  }

  it should "peel off 1st equation -- no xs" in {
    val f = "[$$ a'=y, y'=a$$ & 2=2 & 3=3;]1=1".asFormula
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemHeadT)
    tactic.applicable(node) shouldBe true

    val result = helper.runTactic(tactic, node)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only
      "[$$y'=a, a'≚y$$ & (2=2) & (3=3);][(a'):=y;]1=1".asFormula

  }

  it should "peel off 2nd equation -- no xs" in {
    val f = "[$$y'=a,a'≚y $$ & (2=2) & (3=3);][(a'):=y;]1=1".asFormula
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemHeadT)

    tactic.applicable(node) shouldBe true

    val result = helper.runTactic(tactic, node)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only
      "[$$a'≚y, y'≚a $$ & (2=2) & (3=3);][(y'):=a;][(a'):=y;]1=1".asFormula
  }

  it should "not apply in a variety of conditions" in {
    val f = "[$$x'≚y,y'≚x$$;][(y'):=x;][(x'):=y;]1=1".asFormula
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemHeadT)
    tactic.applicable(node) shouldBe false
  }
//
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff invariant system tail
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  "Diff invariant system tail" should "apply to an appropriate system" in {
    val f = "[$$a'≚y,y'≚a$$  & (2=2) & (3=3);][(y'):=a;][(a'):=y;]1=1".asFormula
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemTailT)

    tactic.applicable(node) shouldBe true

    val result = helper.runTactic(tactic, node)
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[(y'):=a;][(a'):=y;]1=1".asFormula
  }

  it should "not apply to an inappropriate system" in {
    val expected = "[$$a'=y,y'≚a$$ & (2=2) & (3=3);][(y'):=a;][(a'):=y;]1=1".asFormula //just removed the ` from the first equality.
    val node = helper.formulaToNode(expected)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemTailT)
    tactic.applicable(node) shouldBe false
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