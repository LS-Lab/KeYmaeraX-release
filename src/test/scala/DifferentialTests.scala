import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraParser
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import ODETactics.{diffWeakenT, diffWeakenSystemIntroT, diffWeakenSystemHeadT,
  diffWeakenSystemNilT, diffSolution}
import testHelper.StringConverter._
import testHelper.SequentFactory._
import testHelper.ProofFactory._


import scala.collection.immutable.Map


/**
 * Created by nfulton on 12/1/14.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class DifferentialTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  val helper = new ProvabilityTestHelper((x) => println(x))

  //Mathematica
  val mathematicaConfig: Map[String, String] = Map("linkName" -> "/Applications/Mathematica.app/Contents/MacOS/MathKernel")

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.MathematicaScheduler.init(mathematicaConfig)
  }

  override def afterEach() = {
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.MathematicaScheduler.shutdown()
  }

  "differential weaken" should "turn nondeterministic assignments and tests of the evolution domain into facts in the antecedent" in {
    val s = sucSequent("[x'=1 & x>2;]x>0".asFormula)

    val diffWeaken = locateSucc(diffWeakenT)
    getProofSequent(diffWeaken, new RootNode(s)) should be (
      sequent("x_0".asNamedSymbol :: Nil, "x_0>2".asFormula :: Nil, "x_0>0".asFormula :: Nil))
  }

  // alpha renaming not yet done
  ignore should "perform alpha renaming if necessary" in {
    val s = sucSequent("[y'=y & y>2 & z<0;]y>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenT)
    getProofSequent(diffWeaken, new RootNode(s)) should be (
      sequent("y_0".asNamedSymbol :: Nil, "y_0>2 & z<0".asFormula :: Nil, "y_0>0".asFormula :: Nil))
  }

  it should "introduce true if there is no evolution domain constraint" in {
    val s = sucSequent("[x'=1;]x>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenT)
    getProofSequent(diffWeaken, new RootNode(s)) should be (
      sequent("x_0".asNamedSymbol :: Nil, "true".asFormula :: Nil, "x_0>0".asFormula :: Nil))
  }

  // alpha renaming not yet done
  ignore /*"differential weaken of system of ODEs"*/ should "replace system of ODEs with nondeterministic assignments and tests" in {
    val s = sucSequent("[x'=x & x>3, y'=1 & y>2 & z<0;]y>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenT)
    getProofSequent(diffWeaken, new RootNode(s)) should be (
      sequent("x_0".asNamedSymbol :: "y_0".asNamedSymbol :: Nil,
        "y_0>2 & z<0, x_0>3".asFormula :: Nil, "y_0>0".asFormula :: Nil))
  }

  // alpha renaming not yet done
  ignore should "replace system of ODEs with nondeterministic assignments and tests and skolemize correctly" in {
    val s = sucSequent("[x'=x & x>3, y'=1 & y>2 & z<0, z'=2;]y>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenT)
    getProofSequent(diffWeaken, new RootNode(s)) should be (
      sequent("x_0".asNamedSymbol :: "y_0".asNamedSymbol :: "z_0".asNamedSymbol :: Nil,
        "true".asFormula :: "y_0>2 & z_0<0, x_0>3".asFormula :: Nil, "y_0>0".asFormula :: Nil))
  }

  it should "introduce marker when started" in {
    val s = sucSequent("[x'=x & x>3, y'=1 & y>2 & z<0;]y>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenSystemIntroT)
    getProofSequent(diffWeaken, new RootNode(s)) should be (
      sucSequent("[$$x'=x & x>3, y'=1 & y>2&z<0$$;]y>0".asFormula))
  }

  it should "pull out first ODE from marked system" in {
    val s = sucSequent("[$$x'=x & x>3, y'=1 & y>2 & z<0$$;]y>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenSystemHeadT)
    getProofSequent(diffWeaken, new RootNode(s)) should be (
      sucSequent("[x:=*;][$$y'=1 & y>2&z<0$$;][?x>3;]y>0".asFormula))
  }

  // alpha renaming not yet done
  ignore should "pull out first ODE from marked system repeatedly" in {
    val s = sucSequent("[$$x'=x & x>3, y'=1 & y>2 & z<0$$;]y>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenSystemHeadT)
    val node = helper.runTactic(diffWeaken, new RootNode(s))
    node.openGoals().foreach(_.sequent should be (sucSequent("[x:=*;][$$y'=1 & y>2&z<0$$;][?x>3;]y>0".asFormula)))

    val secondNode = helper.runTactic(locateSucc(boxNDetAssign) & locateSucc(skolemizeT) & diffWeaken,
      node.openGoals().head)
    secondNode.openGoals().foreach(_.sequent should be (
      sequent("x_0".asNamedSymbol :: Nil, Nil, "[y:=*;][$$$$;][?y>2&z<0;][?x_0>3;]y>0".asFormula :: Nil)))
  }

  it should "pull out first ODE from marked system and sort in correctly" in {
    val s = sucSequent("[$$x'=1 & x>2 & z<0, z'=2$$;][?x>3;]y>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenSystemHeadT)
    getProofSequent(diffWeaken, new RootNode(s)) should be(
      sucSequent("[x:=*;][$$z'=2$$;][?x>2&z<0;][?x>3;]y>0".asFormula))
  }

  // alpha renaming not yet done
  ignore should "alpha rename if necessary" in {
    val s = sucSequent("[$$y'=1 & y>2 & z<0, z'=2$$;][?x>3;]y>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenSystemHeadT)
    getProofSequent(diffWeaken, new RootNode(s)) should be (
      sucSequent("[y:=*;][$$z'=2$$;][?y>2&z<0;][?x>3;]y>0".asFormula))
  }

  it should "pull out sole ODE from marked system and sort in correctly" in {
    val s = sucSequent("[$$x'=1 & x>2$$;][?x>3;]x>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenSystemHeadT)
    getProofSequent(diffWeaken, new RootNode(s)) should be (sucSequent("[x:=*;][$$$$;][?x>2;][?x>3;]x>0".asFormula))
  }

  // alpha renaming not yet done
  ignore should "alpha rename in sole ODE correctly" in {
    val s = sucSequent("[$$y'=1 & y>2$$;][?x>3;]x>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenSystemHeadT)
    getProofSequent(diffWeaken, new RootNode(s)) should be (sucSequent("[y:=*;][$$$$;][?y>2;][?x>3;]x>0".asFormula))
  }

  it should "remove empty marker" in {
    val s = sucSequent("[$$$$;][?x>3;]y>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenSystemNilT)
    getProofSequent(diffWeaken, new RootNode(s)) should be (sucSequent("[?x>3;]y>0".asFormula))
  }

  // TODO tests that tactics don't pull out without marker

  "differential cut" should "cut formula into NFContEvolve" in {
    val s = sucSequent("[x'=2;]x>0".asFormula)
    val tactic = locateSucc(diffCutT(helper.parseFormula("x>1")))
    getProofSequent(tactic, new RootNode(s)) should be (sucSequent("[x'=2;]x>1 & [x'=2 & (true&x>1);]x>0".asFormula))
  }

  it should "cut formula into evolution domain constraint of rightmost ODE in ContEvolveProduct" in {
    val s = sucSequent("[x'=2, y'=3, z'=4 & y>4;]x>0".asFormula)
    val tactic = locateSucc(diffCutT(helper.parseFormula("x>1")))
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("[x'=2,y'=3,z'=4&y>4;]x>1 & [x'=2,y'=3,z'=4 & (y>4&x>1);]x>0".asFormula))
  }

  it should "cut formula into rightmost ODE in ContEvolveProduct, even if constraint empty" in {
    val s = sucSequent("[x'=2, y'=3;]x>0".asFormula)
    val tactic = locateSucc(diffCutT(helper.parseFormula("x>1")))
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("[x'=2,y'=3;]x>1 & [x'=2,y'=3 & (true&x>1);]x>0".asFormula))
  }

  ignore/*"differential solution tactic"*/ should "use provided solution correctly" in {
    val s = sucSequent("[x0:=x; t:=0; x'=2, t'=1;]x>0".asFormula)

    val diffNode = helper.runTactic(default, new RootNode(s)).openGoals().head
    val tactic = locateSucc(diffSolution(Some("x = x0 + 2*t".asFormula)))
    val node = helper.runTactic(tactic, diffNode)
    node.openGoals()(0).sequent should be (
      sequent("x0".asNamedSymbol :: "t_0".asNamedSymbol :: "x_0".asNamedSymbol :: "t_1".asNamedSymbol :: Nil,
        "t_0=0".asFormula :: Nil, "x_0 = x0 + 2*t".asFormula :: Nil))
    node.openGoals()(1).sequent should be (
      sequent("x0".asNamedSymbol :: "t_0".asNamedSymbol :: "x_0".asNamedSymbol :: "t_1".asNamedSymbol :: Nil,
        // TODO could simplify all those true &
        "t_0=0".asFormula :: "true & x_0 = x0 + 2*t".asFormula :: "true".asFormula :: Nil, "x_0>0".asFormula :: Nil))
  }

  ignore should "use Mathematica to find solution if None is provided" in {
    val s = sucSequent("[x0:=x; t:=0; x'=2, t'=1;]x>0".asFormula)

    val diffNode = helper.runTactic(default, new RootNode(s)).openGoals().head
    // solution = None -> Mathematica
    val tactic = locateSucc(diffSolution(None))
    val node = helper.runTactic(tactic, diffNode)
    node.openGoals()(0).sequent should be (
      sequent("x0".asNamedSymbol :: "t_0".asNamedSymbol :: "x_0".asNamedSymbol :: "t_1".asNamedSymbol :: Nil,
        "t_0=0".asFormula :: Nil,
        // TODO not robust if Mathematica reports equivalent formula but differently formatted
        "x_0 = 2*t + x0 & t_1 = 1*t + t0_0".asFormula :: Nil))
    node.openGoals()(1).sequent should be (
      sequent("x0".asNamedSymbol :: "t_0".asNamedSymbol :: "x_0".asNamedSymbol :: "t_1".asNamedSymbol :: Nil,
        // TODO could simplify all those true &
        "t_0=0".asFormula :: "true & x_0 = 2*t + x0 & t_1 = 1*t + t0_0".asFormula :: "true".asFormula :: Nil,
        "x_0>0".asFormula :: Nil))
  }

  ignore should "prove with differential solution tactic" in {
    import scala.language.postfixOps
    import TacticLibrary.{boxAssignT, skolemizeT, boxSeqT}
    val s = sequent(Nil, "x>0".asFormula :: Nil, "[x0:=x; t:=0; t0:=t; x'=2, t'=1 & t>=0;]x>0".asFormula :: Nil)
    // TODO t:=0 leads to a SubstitutionClashException (because subsequently t'=1)
    val diffNode = helper.runTactic((locateSucc(boxSeqT) ~ locateSucc(boxAssignT))*, new RootNode(s)).openGoals().head
    // TODO when alpha renaming finally works it should be head instead of tail.tail.head
    val postDiffSolNode = helper.runTactic(locateSucc(diffSolution(None)), diffNode).openGoals().tail.tail.head
    helper.runTactic(default, postDiffSolNode) shouldBe 'closed
  }

}
