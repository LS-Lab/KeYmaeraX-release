import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.{HybridProgramTacticsImpl, ODETactics, Tactics, TacticLibrary}
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

  "The axiom-based differential invariant tactic" should "work when there's no test condition" in {
    val f = helper.parseFormula("[x'=1;]z>=0")
    f match {
      case BoxModality(ContEvolveProduct(_: NFContEvolve,_), _) => ()
      case _ => fail("parsed into wrong form.")
    }
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantNormalFormT)

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

  /*
  This is all about the unsound, deprecated approach.

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

//  it should "handle DAEs correctly" in {
//    val f = helper.parseFormula("[$$x'=y & 2=2, y'=x & z>0$$;][?1=1;]p>0")
//    val node = helper.formulaToNode(f)
//    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantHeadEliminationWithTest)
//    require(tactic.applicable(node), "applicable.")
//
//    helper.runTactic(tactic, node)
//
//    val expectedResult = helper.parseFormula("[(x'):=y;][$$y'=x & (z>0)$$;][?1=1&2=2;]p>0")
//    require(!node.openGoals().filter(_.sequent.succ.last == expectedResult).isEmpty)
//  }

  it should "work even when the primed variable isn't x" in {
    val f = helper.parseFormula("[$$y'=notx, notx'=y & z>0$$;][?1=1;]p>0")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantHeadEliminationWithTest)
    require(tactic.applicable(node), "applicable.")

    helper.runTactic(tactic, node)

    val expectedResult = helper.parseFormula("[(y'):=notx;][$$notx'=y & (z>0)$$;][?1=1&true;]p>0")
    require(!node.openGoals().filter(_.sequent.succ.last == expectedResult).isEmpty)
  }

  it should "work even when the primed variable isn't x, but x occurs in the formula" in {
    val f = helper.parseFormula("[$$y'=x, x'=y & z>0$$;][?1=1;]p>0")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantHeadEliminationWithTest)
    require(tactic.applicable(node), "applicable.")

    helper.runTactic(tactic, node)

    val expectedResult = helper.parseFormula("[(y'):=x;][$$x'=y & (z>0)$$;][?1=1&true;]p>0")
    require(!node.openGoals().filter(_.sequent.succ.last == expectedResult).isEmpty)
  }

  it should "apply whenever the post-condition, diff eq system and existing test all contain x's" in {
    val f = helper.parseFormula("[$$x'=y$$;][?x=x;]x>0")
    val node = helper.formulaToNode(f)
    helper.runTactic(helper.positionTacticToTactic(ODETactics.diffInvariantHeadEliminationWithTest), node)

    val expectedResult = helper.parseFormula("[x':=y;][?x=x&true;]x>0")
    require(!node.openGoals().filter(_.sequent.succ.last == expectedResult).isEmpty)
  }

  // Head elimination (no test)
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  "Head eliminiation (no test)" should "not apply when there's a test" in {
    val f = helper.parseFormula("[$$y'=notx, notx'=y & z>0$$;][?true;]p>0")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantHeadEliminationNoTest)
    require(!tactic.applicable(node))
  }

  it should "apply and peel off a system correctly in the simplest case" in {
    val f = helper.parseFormula("[$$x'=y, y'=x & z>0$$;]p>0")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantHeadEliminationNoTest)

    require(tactic.applicable(node), "applicable.")

    helper.runTactic(tactic, node)

    val expectedResult = helper.parseFormula("[(x'):=y;][$$y'=x & (z>0)$$;][?true;]p>0")
    require(!node.openGoals().filter(_.sequent.succ.last == expectedResult).isEmpty)
  }

  it should "apply whenever the system is x'=theta and the post-condition contains an x" in {
    val f = helper.parseFormula("[$$x'=1$$;]x>0")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantHeadEliminationNoTest)
    require(tactic.applicable(node), "applicable")
    helper.runTactic(tactic, node)

    val expectedResult = helper.parseFormula("[x':=1;][?true;]x>0")
    require(!node.openGoals().filter(_.sequent.succ.last == expectedResult).isEmpty)
  }

  it should "handle DAEs correctly" in {
    val f = helper.parseFormula("[$$x'=y & 2=2, y'=x & z>0$$;]p>0")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantHeadEliminationNoTest)
    require(tactic.applicable(node), "applicable.")

    helper.runTactic(tactic, node)

    val expectedResult = helper.parseFormula("[(x'):=y;][$$y'=x & (z>0)$$;][?2=2;]p>0")
    require(!node.openGoals().filter(_.sequent.succ.last == expectedResult).isEmpty)
  }
//
//  it should "work even when the primed variable isn't x" in {
//    val f = helper.parseFormula("[$$y'=notx, notx'=y & z>0$$;]p>0")
//    val node = helper.formulaToNode(f)
//    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantHeadEliminationNoTest)
//    require(tactic.applicable(node), "applicable.")
//
//    helper.runTactic(tactic, node)
//
//    val expectedResult = helper.parseFormula("[(y'):=notx;][$$notx'=y & (z>0)$$;][?true;]p>0")
//    require(!node.openGoals().filter(_.sequent.succ.last == expectedResult).isEmpty)
//  }
//
//
//  it should "work even when the primed variable isn't x, but x occurs in the formula" in {
//    val f = helper.parseFormula("[$$y'=x, x'=y & z>0$$;]p>0")
//    val node = helper.formulaToNode(f)
//    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantHeadEliminationNoTest)
//    require(tactic.applicable(node), "applicable.")
//
//    helper.runTactic(tactic, node)
//
//    val expectedResult = helper.parseFormula("[(y'):=x;][$$x'=y & (z>0)$$;][?true;]p>0")
//    require(!node.openGoals().filter(_.sequent.succ.last == expectedResult).isEmpty)
//  }

  // Nil elimination
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  "Nil Elimination Axiom" should "not apply when there's still a system there" in {
    val f = helper.parseFormula("[$$y'=notx, notx'=y & z>0$$;][?1=1;]p>0")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantNilElimination)
    require(!tactic.applicable(node))
  }

  it should "apply when the system starts off empty." in {
    val f = helper.parseFormula("[$$$$;][?true;]true")
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantNilElimination)
    require(!tactic.applicable(helper.formulaToNode(f)))
  }

  it should "apply" in {
    val f = helper.parseFormula("[$$$$;][?true;](x>0)'")
    require(!helper.positionTacticToTactic(ODETactics.diffInvariantNilElimination).applicable(helper.formulaToNode(f)))
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff invariant where the invariant is input.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //Validating concerns from conversation with Stefan.
  "Diff Assign" should "apply to something silly" in {
    val f = helper.parseFormula("[x':=0;]notx=notx")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(TacticLibrary.boxDerivativeAssignT)
    assert(tactic.applicable(node), "box derivative assignment tactic should be applicable.")
    helper.runTactic(tactic, node)
    helper.runTactic(tactic, node)
  }

//  //This may not necessarily be true.
//  it should "apply assignment to postcondition" in {
//    val f = helper.parseFormula("[x' := 1;]x'=1")
//    println(f.toString())
//    val node = helper.formulaToNode(f)
//    val tactic = helper.positionTacticToTactic(TacticLibrary.boxDerivativeAssignT)
//    assert(tactic.applicable(node), "Box derivative assignment tactic should be applicable.")
//    helper.runTactic(tactic, node) //@todo Of course this fails because diffAssign isn't part of the default tactic.
//    println(helper.report(node))
//  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff invariant where the invariant is input.
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  */

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff invariant system introduction'
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff invariant system head'
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff invariant system tail'
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


}