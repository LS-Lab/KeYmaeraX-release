import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.{ODETactics, Tactics, TacticLibrary}
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

  var tool: Mathematica = null
  val mathematicaConfig = helper.mathematicaConfig

  override def beforeEach() = {
    tool = new Mathematica
    tool.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.MathematicaScheduler.init(mathematicaConfig)
  }

  override def afterEach() = {
    tool.shutdown()
    tool = null
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.MathematicaScheduler.shutdown()
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Differential invariants where invariant is already part of the formula? @todo
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  "The axiom-based differential invariant tactic" should "simplest example" in {
    val f = helper.parseFormula("[x'=1 & z>0;]z>=0")
    f match {
      case BoxModality(_: NFContEvolve, _) => ()
      case _ => fail("f doesn't match the applicability condition.")
    }

    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(TacticLibrary.axdiffInvNormalFormT)

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

//  //This would occasionally fail with message SubstitutionClashException: clash in uniform subst b/c free vars Set(x)
//  //have been bound when applying replacement x>z.
//  it should "allow the constraint to contain the primed variable" in {
//    val f = helper.parseFormula("[x'=1 & z>x;]z>=0")
//    f match {
//      case BoxModality(_: NFContEvolve, _) => ()
//      case _ => fail("f doesn't match the applicability condition.")
//    }
//
//    val node = helper.formulaToNode(f)
//    val tactic = helper.positionTacticToTactic(TacticLibrary.axdiffInvNormalFormT)
//
//    tactic.applicable(node) should be (true)
//    try {
//      helper.runTactic(tactic, node)
//    }
//    catch {
//      case e: Exception => fail("Expected no exceptions.")
//    }
//
//    val expectedResult = helper.parseFormula("[x'=1 & (z>x);](z>x->[(x'):=1;](z>=0)')")
//
//    require(node.openGoals().map(pn => {
//      val f = pn.sequent.succ.last
//      f == expectedResult
//    }).contains(true))
//
//    fail("still getting that error. Is it only occasional?")
//  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // DiffEq Systems axioms - in isolation
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  // Cursor introduction
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  "DI System Introduction" should "introduce the systems marker" in {
    val f = helper.parseFormula("[x' = y, y' = x & x<5;]x>0")
    val node = helper.formulaToNode(f)
    helper.runTactic(helper.positionTacticToTactic(ODETactics.diffInvariantSystemIntroduction),node)

    require(node.openGoals().map(g => g.sequent.succ.last match {
      case BoxModality(IncompleteSystem(_), _) => true
      case _=> false
    }).contains(true))
  }

  it should "introduce the systems marker (long system with no tests)" in {
    val f = helper.parseFormula("[x' = y, y' = x;]x>0")
    val node = helper.formulaToNode(f)
    helper.runTactic(helper.positionTacticToTactic(ODETactics.diffInvariantSystemIntroduction),node)

    require(node.openGoals().map(g => g.sequent.succ.last match {
      case BoxModality(IncompleteSystem(_), _) => true
      case _=> false
    }).contains(true))
  }

  it should "not apply to short systems" in {
    val f = helper.parseFormula("[x' = y & x>0;]x>0")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemIntroduction)
    tactic.applicable(node) should be (false)
  }

  it should "Not apply to a system without multiple equations" in {
    val f = helper.parseFormula("[x' = y;]x>0")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemIntroduction)
    tactic.applicable(node) should be (false)
  }

  // Head elimination (with test)
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  "Head Elimination with test" should "apply and peel off a system correctly in the simplest case" in {
    val f = helper.parseFormula("[$$x'=y, y'=x & z>0$$;][?1=1;]p>0")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantHeadEliminationWithTest)
    require(tactic.applicable(node), "applicable.")

    helper.runTactic(tactic, node)

    val expectedResult = helper.parseFormula("[(x'):=y;][$$y'=x & (z>0)$$;][?1=1&true;]p>0")
    require(!node.openGoals().filter(_.sequent.succ.last == expectedResult).isEmpty)
  }

  it should "handle DAEs correctly" in {
    val f = helper.parseFormula("[$$x'=y & 2=2, y'=x & z>0$$;][?1=1;]p>0")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantHeadEliminationWithTest)
    require(tactic.applicable(node), "applicable.")

    helper.runTactic(tactic, node)

    val expectedResult = helper.parseFormula("[(x'):=y;][$$y'=x & (z>0)$$;][?1=1&2=2;]p>0")
    require(!node.openGoals().filter(_.sequent.succ.last == expectedResult).isEmpty)
  }

  it should "work even when the primed variable isn't x" in {
    val f = helper.parseFormula("[$$y'=notx, notx'=y & z>0$$;][?1=1;]p>0")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantHeadEliminationWithTest)
    require(tactic.applicable(node), "applicable.")

    helper.runTactic(tactic, node)

    val expectedResult = helper.parseFormula("[(y'):=notx;][$$notx'=y & (z>0)$$;][?1=1&true;]p>0")
    require(!node.openGoals().filter(_.sequent.succ.last == expectedResult).isEmpty)
  }

  it should "work even when the primed variable isn't x BUT x occurs in the formula" in {
    val f = helper.parseFormula("[$$y'=x, x'=y & z>0$$;][?1=1;]p>0")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantHeadEliminationWithTest)
    require(tactic.applicable(node), "applicable.")

    helper.runTactic(tactic, node)

    val expectedResult = helper.parseFormula("[(y'):=x;][$$x'=y & (z>0)$$;][?1=1&true;]p>0")
    require(!node.openGoals().filter(_.sequent.succ.last == expectedResult).isEmpty)
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Combining systems of differential equations with the differential invariant axioms
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //@todo Friday morning


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff invariant where the invariant is input.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  //@todo Friday afternoon

}