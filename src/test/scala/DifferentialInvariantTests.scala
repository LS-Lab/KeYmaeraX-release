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

  private def containsOpenGoal(node:ProofNode, f:Formula) =
    !node.openGoals().find(_.sequent.succ.contains(f)).isEmpty

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Differential invariants where invariant is already part of the formula? @todo
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  "The axiom-based differential invariant tactic" should "work when there IS a test condition (no tests when there is none..." in {
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
    require(containsOpenGoal(node, expected))
  }

  it should "introduce a marker when there are interleaved tests" in {
    val f=  helper.parseFormula("[x'=y & 2=2, y'=x & 3=3;]1=1")
    val node = helper.formulaToNode(f)

    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemIntroT)
    assert(tactic.applicable(node))
    helper.runTactic(tactic, node)

    val expected = helper.parseFormula("1=1&[$$x'=y & 2=2,y'=x & 3=3$$;](1=1)'")
    require(containsOpenGoal(node, expected))
  }

//  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  // Diff invariant system head no test
//  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//  "Diff invariant system head no test" should "not fail tests because of broken equality" in {
//    val expected = helper.parseFormula("[$$y'=x & true,x'=`y & true$$;][(x'):=y;]1=1->[$$x'=y & true,y'=x & true$$;]1=1")
//    val result   = helper.parseFormula("[$$y'=x & true,x'=`y & true$$;][(x'):=y;]1=1->[$$x'=y & true,y'=x & true$$;]1=1")
//    require(expected.equals(result))
//    require(expected == result)
//  }
//
//  it should "peel off 1st equation" in {
//    val f = helper.parseFormula("[$$ x'=y, y'=x$$;]1=1")
//    val node = helper.formulaToNode(f)
//    val tactic = helper.positionTacticToTactic(ODETactics.diffInvSystemHeadNoTest)
//    require(tactic.applicable(node))
//
//    helper.runTactic(tactic,node)
//    val expected = helper.parseFormula("[$$y'=x & true,x' =` y & true$$;][(x'):=y;]1=1")
//
//    require(containsOpenGoal(node,expected))
//  }
//
//  it should "peel off 2nd equation" in {
//    val f = helper.parseFormula("[$$y'=x,x' =` y$$;][(x'):=y;]1=1") //expected from last test case minus the tests.
//    val node = helper.formulaToNode(f)
//    val tactic = helper.positionTacticToTactic(ODETactics.diffInvSystemHeadNoTest)
//    require(tactic.applicable(node))
//
//    helper.runTactic(tactic,node)
//    val expected = helper.parseFormula("[$$x'=`y & true,y'=`x & true$$;][(y'):=x;][(x'):=y;]1=1")
//    require(containsOpenGoal(node,expected))
//  }
//
//
//  it should "peel off 1st equation -- no x's" in {
//    val f = helper.parseFormula("[$$ a'=y, y'=a$$;]1=1")
//    val node = helper.formulaToNode(f)
//    val tactic = helper.positionTacticToTactic(ODETactics.diffInvSystemHeadNoTest)
//    require(tactic.applicable(node))
//
//    helper.runTactic(tactic,node)
//    val expected = helper.parseFormula("[$$y'=a & true,a' =` y & true$$;][(a'):=y;]1=1")
//
//    require(containsOpenGoal(node,expected))
//  }
//
//  it should "peel off 2nd equation -- no x's" in {
//    val f = helper.parseFormula("[$$y'=a,a' =` y$$;][(a'):=y;]1=1") //expected from last test case minus the tests.
//    val node = helper.formulaToNode(f)
//    val tactic = helper.positionTacticToTactic(ODETactics.diffInvSystemHeadNoTest)
//    require(tactic.applicable(node))
//
//    helper.runTactic(tactic,node)
//    val expected = helper.parseFormula("[$$a'=`y & true,y'=`a & true$$;][(y'):=a;][(a'):=y;]1=1")
//    require(containsOpenGoal(node,expected))
//  }
//
//  it should "not apply to a completed system" in {
//    val f = helper.parseFormula("[$$x'=`y & true,y'=`x & true$$;][(y'):=x;][(x'):=y;]1=1")
//    val node = helper.formulaToNode(f)
//    val tactic = helper.positionTacticToTactic(ODETactics.diffInvSystemHeadNoTest)
//    require(!tactic.applicable(node))
//  }


  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff invariant system head test
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

  "Diff invariant system head test" should "peel off 1st equation" in {
    val f = helper.parseFormula("[$$ x'=y & 2=2, y'=x & 3=3$$;]1=1")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemHeadT)
    require(tactic.applicable(node))

    helper.runTactic(tactic, node)

    val expected = helper.parseFormula("[$$y'=x & (3=3),x'=`y & (2=2)$$;][(x'):=y;](2=2->1=1)")
    require(containsOpenGoal(node,expected))
  }

  it should "peel off 2nd equation" in {
    val f = helper.parseFormula("[$$y'=x & 3=3,x' =` y & 2=2$$;][(x'):=y;]1=1")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemHeadT)
    require(tactic.applicable(node))

    helper.runTactic(tactic, node)

    val expected = helper.parseFormula("[$$x'=`y & (2=2),y'=`x & (3=3)$$;][(y'):=x;](3=3->[(x'):=y;]1=1)")
    require(containsOpenGoal(node,expected))
  }

  it should "peel off 1st equation -- no xs" in {
    val f = helper.parseFormula("[$$ a'=y & 2=2, y'=a & 3=3$$;]1=1")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemHeadT)
    require(tactic.applicable(node))

    helper.runTactic(tactic, node)

    val expected = helper.parseFormula("[$$y'=a & (3=3),a'=`y & (2=2)$$;][(a'):=y;](2=2->1=1)")
    require(containsOpenGoal(node,expected))
  }

  it should "peel off 2nd equation -- no xs" in {
    val f = helper.parseFormula("[$$y'=a & (3=3),a'=`y & (2=2)$$;][(a'):=y;](2=2->1=1)")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemHeadT)
    require(tactic.applicable(node))

    helper.runTactic(tactic, node)

    val expected = helper.parseFormula("[$$a'=`y & (2=2),y'=`a & (3=3)$$;][(y'):=a;](3=3->[(a'):=y;](2=2->1=1))")
    require(containsOpenGoal(node,expected))
  }

  it should "not apply in a variety of conditions" in {
    val f = helper.parseFormula("[$$x'=`y & true,y'=`x & true$$;][(y'):=x;][(x'):=y;]1=1")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemHeadT)
    require(!tactic.applicable(node))
  }
//
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff invariant system tail
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  "Diff invariant system tail" should "apply to an appropriate system" in {
    val expected = helper.parseFormula("[$$a'=`y & (2=2),y'=`a & (3=3)$$;][(y'):=a;](3=3->[(a'):=y;]1=1)")
    val node = helper.formulaToNode(expected)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemTailT)
    require(tactic.applicable(node))

  }

  it should "not apply to an inappropriate system" in {
    val expected = helper.parseFormula("[$$a'=y & (2=2),y'=`a & (3=3)$$;][(y'):=a;](3=3->[(a'):=y;]1=1)") //just removed the ` from the first equality.
    val node = helper.formulaToNode(expected)
    val tactic = helper.positionTacticToTactic(ODETactics.diffInvariantSystemTailT)
    require(!tactic.applicable(node))
  }

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Diff invariant system general
  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  "General diff invariant" should "work when we're on a circle and want to stay on the circle." in {
    val f = helper.parseFormula("[x'=y, y'=x & x^2 + y^2 = 1;]x^2 + y^2 = 1")
    val node = helper.formulaToNode(f)
    val tactic = helper.positionTacticToTactic(TacticLibrary.diffInvariantSystem)
    require(tactic.applicable(node))

    helper.runTactic(tactic,node)
    helper.report(node)
  }

}