import edu.cmu.cs.ls.keymaera.core._
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
      sequent("x".asNamedSymbol :: Nil, "x>2".asFormula :: Nil, "x>0".asFormula :: Nil))
  }

  it should "perform alpha renaming if necessary" in {
    val s = sucSequent("[y'=y & y>2 & z<0;]y>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenT)
    getProofSequent(diffWeaken, new RootNode(s)) should be (
      sequent("y".asNamedSymbol :: Nil, "y>2 & z<0".asFormula :: Nil, "y>0".asFormula :: Nil))
  }

  it should "introduce true if there is no evolution domain constraint" in {
    val s = sucSequent("[x'=1;]x>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenT)
    getProofSequent(diffWeaken, new RootNode(s)) should be (
      sequent("x".asNamedSymbol :: Nil, "true".asFormula :: Nil, "x>0".asFormula :: Nil))
  }

  "differential weaken of system of ODEs" should "replace system of ODEs with nondeterministic assignments and tests" in {
    val s = sucSequent("[x'=x & x>3, y'=1 & y>2 & z<0;]y>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenT)
    getProofSequent(diffWeaken, new RootNode(s)) should be (
      sequent("x".asNamedSymbol :: "y".asNamedSymbol :: Nil,
        "y>2 & z<0".asFormula :: "x>3".asFormula :: Nil, "y>0".asFormula :: Nil))
  }

  it should "replace system of ODEs with nondeterministic assignments and tests and skolemize correctly" in {
    val s = sucSequent("[x'=x+y & x>3, y'=1 & y>2 & z<0, z'=2;]y>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenT)
    getProofSequent(diffWeaken, new RootNode(s)) should be (
      sequent("x".asNamedSymbol :: "y".asNamedSymbol :: "z".asNamedSymbol :: Nil,
        "true".asFormula :: "y>2 & z<0".asFormula :: "x>3".asFormula :: Nil, "y>0".asFormula :: Nil))
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

  it should "pull out first ODE from marked system repeatedly" in {
    val s = sucSequent("[$$x'=x & x>3, y'=1 & y>2 & z<0$$;]y>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenSystemHeadT)
    val node = helper.runTactic(diffWeaken, new RootNode(s))
    node.openGoals().foreach(_.sequent should be (sucSequent("[x:=*;][$$y'=1 & y>2&z<0$$;][?x>3;]y>0".asFormula)))

    val secondNode = helper.runTactic(locateSucc(boxNDetAssign) & diffWeaken, node.openGoals().head)
    secondNode.openGoals().foreach(_.sequent should be (
      sequent("x".asNamedSymbol :: Nil, Nil, "[y:=*;][$$$$;][?y>2&z<0;][?x>3;]y>0".asFormula :: Nil)))
  }

  it should "pull out first ODE from marked system and sort in correctly" in {
    val s = sucSequent("[$$x'=1 & x>2 & z<0, z'=2$$;][?x>3;]y>0".asFormula)
    val diffWeaken = locateSucc(diffWeakenSystemHeadT)
    getProofSequent(diffWeaken, new RootNode(s)) should be(
      sucSequent("[x:=*;][$$z'=2$$;][?x>2&z<0;][?x>3;]y>0".asFormula))
  }

  it should "alpha rename if necessary" in {
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

  it should "alpha rename in sole ODE correctly" in {
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

  "differential solution tactic" should "use Mathematica to find solution if None is provided" in {
    val s = sequent(Nil, "b=0".asFormula :: "x>b".asFormula :: Nil, "[x'=2;]x>b".asFormula :: Nil)

    // solution = None -> Mathematica
    val tactic = locateSucc(diffSolution(None))

    getProofSequent(tactic, new RootNode(s)) should be (
      sequent("k4_t_1".asNamedSymbol :: "x_2".asNamedSymbol :: "k4_t_4".asNamedSymbol :: "x_3".asNamedSymbol ::
              "k4_t_5".asNamedSymbol :: "x_4".asNamedSymbol :: /*"k4_t_6".asNamedSymbol ::*/ Nil,
        // TODO could simplify all those true &
        // TODO not robust if Mathematica reports equivalent formula but differently formatted
        "b=0".asFormula :: "x>b".asFormula :: "k4_t_1=0".asFormula :: "x_2=x".asFormula :: "k4_t_4=k4_t_1".asFormula ::
          "true".asFormula :: "true".asFormula :: "true".asFormula ::
          "true&(x_3=2*k4_t_5 + x_4 & k4_t_5 >= k4_t_4)".asFormula :: Nil,
        "x_3>b".asFormula :: Nil))
  }

  it should "find solutions for x'=v, v'=a if None is provided" in {
    val s = sequent(Nil, "x>0".asFormula :: Nil, "[x'=v, v'=a;]x>0".asFormula :: Nil)

    // solution = None -> Mathematica
    val tactic = locateSucc(diffSolution(None))

    val node = getProofSequent(tactic, new RootNode(s))
    fail()
    // TODO check expected result
  }

  it should "not introduce time if already present" in {
    val s = sequent(Nil, "x>0".asFormula :: "t=0".asFormula :: Nil, "[x'=2, t'=1;]x>0".asFormula :: Nil)

    // solution = None -> Mathematica
    val tactic = locateSucc(diffSolution(None))
    getProofSequent(tactic, new RootNode(s)) should be (
      sequent("x_2".asNamedSymbol :: "t_2".asNamedSymbol :: "x_3".asNamedSymbol :: "t_3".asNamedSymbol :: Nil,
        // TODO could simplify all those true &
        // TODO not robust if Mathematica reports equivalent formula but differently formatted
        "x>0".asFormula :: "t=0".asFormula :: "x_2=x".asFormula :: "t_2=t".asFormula ::
          "true & x_3=2*(t_3-t_2)+x_2 & t_3>=t_2".asFormula :: "true".asFormula :: Nil,
        "x_0>0".asFormula :: Nil))
  }

  it should "preserve time evolution domain constraints when using Mathematica to find solution" in {
    val s = sequent(Nil, "x>0".asFormula :: "t=0".asFormula :: Nil, "[x'=2, t'=1 & t<=5;]x>0".asFormula :: Nil)

    // solution = None -> Mathematica
    val tactic = locateSucc(diffSolution(None))
    getProofSequent(tactic, new RootNode(s)) should be (
      sequent("x_2".asNamedSymbol :: "t_2".asNamedSymbol :: "x_3".asNamedSymbol :: "t_3".asNamedSymbol :: Nil,
        // TODO could simplify all those true &
        // TODO not robust if Mathematica reports equivalent formula but differently formatted
        "x>0".asFormula :: "t=0".asFormula :: "x_2=x".asFormula :: "t_2=t".asFormula ::
          "t_3<=5 & x_3=2*t_3+x_2 & t_3>=t_2".asFormula :: "true".asFormula :: Nil,
        "x_0>0".asFormula :: Nil))
  }

  it should "prove with differential solution tactic" in {
    import scala.language.postfixOps
    import TacticLibrary.{boxAssignT, boxSeqT}
    val s = sucSequent("x>0 -> [t:=0; x'=2, t'=1;]x>0".asFormula)
    val diffNode = helper.runTactic(locateSucc(ImplyRightT) & locateSucc(boxSeqT) & locateSucc(boxAssignT),
      new RootNode(s)).openGoals().head
    val postDiffSolNode = helper.runTactic(locateSucc(diffSolution(None)), diffNode).openGoals().head
    helper.runTactic(default, postDiffSolNode) shouldBe 'closed
  }

  "Differential auxiliaries tactic" should "add y'=1 to [x'=2]x>0" in {
    import ODETactics.diffAuxiliaryT
    val s = sucSequent("[x'=2;]x>0".asFormula)
    val tactic = locateSucc(diffAuxiliaryT(Variable("y", None, Real), "0".asTerm, "1".asTerm))
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("(x>0 <-> \\exists y. x>0) & [x'=2,y'=0*y+1;]x>0".asFormula)
    )
  }

  it should "add y'=x*y+z to [x'=x+2*z]x>0" in {
    import ODETactics.diffAuxiliaryT
    val s = sucSequent("[x'=2;]x>0".asFormula)
    val tactic = locateSucc(diffAuxiliaryT(Variable("y", None, Real), "x".asTerm, "z".asTerm))
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("(x>0 <-> \\exists y. x>0) & [x'=2,y'=x*y+z;]x>0".asFormula)
    )
  }

  it should "use a provided safety predicate" in {
    import ODETactics.diffAuxiliaryT
    val s = sucSequent("[x'=2;]x>0".asFormula)
    val tactic = locateSucc(diffAuxiliaryT(Variable("y", None, Real), "x".asTerm, "z".asTerm, Some("y>2*x".asFormula)))
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("(x>0 <-> \\exists y. y>2*x) & [x'=2,y'=x*y+z;]y>2*x".asFormula)
    )
  }

  it should "not allow non-linear ghosts (1)" in {
    import ODETactics.diffAuxiliaryT
    val s = sucSequent("[x'=2;]x>0".asFormula)
    val tactic = locateSucc(diffAuxiliaryT(Variable("y", None, Real), "y".asTerm, "1".asTerm))
    tactic.applicable(new RootNode(s)) should be (false)
  }

  it should "not allow non-linear ghosts (2)" in {
    import ODETactics.diffAuxiliaryT
    val s = sucSequent("[x'=2;]x>0".asFormula)
    val tactic = locateSucc(diffAuxiliaryT(Variable("y", None, Real), "1".asTerm, "y".asTerm))
    tactic.applicable(new RootNode(s)) should be (false)
  }

  it should "not allow ghosts that are already present in the ODE" in {
    import ODETactics.diffAuxiliaryT
    val s = sucSequent("[x'=2;]x>0".asFormula)
    val tactic = locateSucc(diffAuxiliaryT(Variable("x", None, Real), "0".asTerm, "1".asTerm))
    tactic.applicable(new RootNode(s)) should be (false)
  }

}
