import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import ODETactics.{diffWeakenT, diffWeakenAxiomT, diffSolution, diamondDiffWeakenAxiomT}
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
  val mathematicaConfig: Map[String, String] = helper.mathematicaConfig

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

  "Box differential weaken tactic" should "pull out evolution domain constraint" in {
    val s = sucSequent("[x'=1 & x>2;]x>0".asFormula)

    val diffWeakenAx = locateSucc(diffWeakenAxiomT)
    getProofSequent(diffWeakenAx, new RootNode(s)) should be (sucSequent("[x'=1 & x>2;](x>2 -> x>0)".asFormula))

    val diffWeaken = locateSucc(diffWeakenT)
    val result = helper.runTactic(diffWeaken, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>2 -> x>0".asFormula
  }

  it should "perform alpha renaming if necessary" in {
    val s = sucSequent("[y'=y & y>2 & z<0;]y>0".asFormula)
    val diffWeakenAx = locateSucc(diffWeakenAxiomT)
    val result = helper.runTactic(diffWeakenAx, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[y'=y & y>2 & z<0;](y>2 & z<0 -> y>0)".asFormula

    val diffWeaken = locateSucc(diffWeakenT)
    val result2 = helper.runTactic(diffWeaken, new RootNode(s))
    result2.openGoals() should have size 1
    result2.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result2.openGoals().flatMap(_.sequent.succ) should contain only "y>2 & z<0 -> y>0".asFormula
  }

  it should "introduce true if there is no evolution domain constraint" in {
    val s = sucSequent("[x'=1;]x>0".asFormula)
    val diffWeakenAx = locateSucc(diffWeakenAxiomT)
    val result = helper.runTactic(diffWeakenAx, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x'=1;](true -> x>0)".asFormula

    val diffWeaken = locateSucc(diffWeakenT)
    val result2 = helper.runTactic(diffWeaken, new RootNode(s))
    result2.openGoals() should have size 1
    result2.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result2.openGoals().flatMap(_.sequent.succ) should contain only "true -> x>0".asFormula
  }

  "Diamond differential weaken tactic" should "pull out evolution domain constraint" in {
    val s = sucSequent("<x'=1 & x>2;>x>0".asFormula)

    val diffWeakenAx = locateSucc(diamondDiffWeakenAxiomT)
    getProofSequent(diffWeakenAx, new RootNode(s)) should be (sucSequent("<x'=1 & x>2;>(!(x>2 -> !x>0))".asFormula))

//    val diffWeaken = locateSucc(diffWeakenT)
//    val result = helper.runTactic(diffWeaken, new RootNode(s))
//    result.openGoals() should have size 1
//    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
//    result.openGoals().flatMap(_.sequent.succ) should contain only "x>2 -> x>0".asFormula
  }

  it should "work inside formula" in {
    val s = sucSequent("x>0 & <x'=1 & x>2;>x>0".asFormula)

    val diffWeakenAx = diamondDiffWeakenAxiomT(SuccPosition(0, PosInExpr(1::Nil)))
    getProofSequent(diffWeakenAx, new RootNode(s)) should be (sucSequent("x>0 & <x'=1 & x>2;>(!(x>2 -> !x>0))".asFormula))

    //    val diffWeaken = locateSucc(diffWeakenT)
    //    val result = helper.runTactic(diffWeaken, new RootNode(s))
    //    result.openGoals() should have size 1
    //    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    //    result.openGoals().flatMap(_.sequent.succ) should contain only "x>2 -> x>0".asFormula
  }

  "differential weaken of system of ODEs" should "pull out evolution domain constraint" in {
    val s = sucSequent("[x'=x, y'=1 & y>2 & z<0;]y>0".asFormula)
    val diffWeakenAx = locateSucc(diffWeakenAxiomT)
    getProofSequent(diffWeakenAx, new RootNode(s)) should be (sucSequent("[x'=x, y'=1 & y>2 & z<0;](y>2 & z<0 -> y>0)".asFormula))

    val diffWeaken = locateSucc(diffWeakenT)
    val result = helper.runTactic(diffWeaken, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "y>2 & z<0 -> y>0".asFormula
  }

  it should "also work when the ODEs are interdependent" in {
    val s = sucSequent("[x'=x+y, y'=1, z'=2 & y>2 & z<0;]y>0".asFormula)
    val diffWeakenAx = locateSucc(diffWeakenAxiomT)
    getProofSequent(diffWeakenAx, new RootNode(s)) should be (
      sucSequent("[x'=x+y, y'=1, z'=2 & y>2 & z<0;](y>2 & z<0 -> y>0)".asFormula))

    val diffWeaken = locateSucc(diffWeakenT)
    val result = helper.runTactic(diffWeaken, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "y>2 & z<0 -> y>0".asFormula
  }

  it should "also work inside formulas" in {
    val s = sucSequent("x>0 & [x'=1 & y>2;]y>0".asFormula)
    val diffWeakenAx = diffWeakenAxiomT(SuccPosition(0, PosInExpr(1::Nil)))
    getProofSequent(diffWeakenAx, new RootNode(s)) should be (
      sucSequent("x>0 & [x'=1 & y>2;](y>2 -> y>0)".asFormula))

    // TODO tactic with abstraction etc.
  }

  "differential cut" should "cut in a simple formula" in {
    import ODETactics.diffCutT
    val s = sucSequent("[x'=2;]x>=0".asFormula)
    val tactic = locateSucc(diffCutT("x>0".asFormula))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 2
    result.openGoals()(0).sequent.ante shouldBe empty
    result.openGoals()(0).sequent.succ should contain only "[x'=2;]x>0".asFormula
    result.openGoals()(0).tacticInfo.infos.get("branchLabel") shouldBe Some(BranchLabels.cutShowLbl)
    result.openGoals()(1).sequent.ante shouldBe empty
    result.openGoals()(1).sequent.succ should contain only "[x'=2 & true & x>0;]x>=0".asFormula
    result.openGoals()(1).tacticInfo.infos.get("branchLabel") shouldBe Some(BranchLabels.cutUseLbl)
  }

  it should "cut formula into evolution domain constraint of rightmost ODE in ODEProduct" in {
    val s = sucSequent("[x'=2, y'=3, z'=4 & y>4;]x>0".asFormula)
    val tactic = locateSucc(diffCutT("x>1".asFormula))

    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 2
    result.openGoals()(0).sequent.ante shouldBe empty
    result.openGoals()(0).sequent.succ should contain only "[x'=2,y'=3,z'=4 & y>4;]x>1".asFormula
    result.openGoals()(0).tacticInfo.infos.get("branchLabel") shouldBe Some(BranchLabels.cutShowLbl)
    result.openGoals()(1).sequent.ante shouldBe empty
    result.openGoals()(1).sequent.succ should contain only "[x'=2,y'=3,z'=4 & (y>4&x>1);]x>0".asFormula
    result.openGoals()(1).tacticInfo.infos.get("branchLabel") shouldBe Some(BranchLabels.cutUseLbl)
  }

  it should "cut formula into rightmost ODE in ODEProduct, even if constraint empty" in {
    val s = sucSequent("[x'=2, y'=3;]x>0".asFormula)
    val tactic = locateSucc(diffCutT("x>1".asFormula))

    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 2
    result.openGoals()(0).sequent.ante shouldBe empty
    result.openGoals()(0).sequent.succ should contain only "[x'=2, y'=3;]x>1".asFormula
    result.openGoals()(0).tacticInfo.infos.get("branchLabel") shouldBe Some(BranchLabels.cutShowLbl)
    result.openGoals()(1).sequent.ante shouldBe empty
    result.openGoals()(1).sequent.succ should contain only "[x'=2,y'=3 & (true&x>1);]x>0".asFormula
    result.openGoals()(1).tacticInfo.infos.get("branchLabel") shouldBe Some(BranchLabels.cutUseLbl)
  }

  it should "preserve existing evolution domain constraint" in {
    import ODETactics.diffCutT
    val s = sucSequent("[x'=2 & x>=0 | y<z;]x>=0".asFormula)
    val tactic = locateSucc(diffCutT("x>0".asFormula))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 2
    result.openGoals()(0).sequent.ante shouldBe empty
    result.openGoals()(0).sequent.succ should contain only "[x'=2 & x>=0 | y<z;]x>0".asFormula
    result.openGoals()(0).tacticInfo.infos.get("branchLabel") shouldBe Some(BranchLabels.cutShowLbl)
    result.openGoals()(1).sequent.ante shouldBe empty
    result.openGoals()(1).sequent.succ should contain only "[x'=2 & (x>=0 | y<z) & x>0;]x>=0".asFormula
    result.openGoals()(1).tacticInfo.infos.get("branchLabel") shouldBe Some(BranchLabels.cutUseLbl)
  }

  "differential solution tactic" should "use Mathematica to find solution if None is provided" in {
    val s = sequent(Nil, "b=0 & x>b".asFormula :: Nil, "[x'=2;]x>b".asFormula :: Nil)

    // solution = None -> Mathematica
    val tactic = locateSucc(diffSolution(None))

    val node = helper.runTactic(tactic, new RootNode(s))

    node.openGoals() should have size 1
    node.openGoals().flatMap(_.sequent.ante) should contain only (
      "b=0 & x>b".asFormula,
      "k4_t_1=0".asFormula,
      "x_2()=x".asFormula,
      "k4_t_4()=k4_t_1".asFormula
      )
    node.openGoals().flatMap(_.sequent.succ) should contain only
      "true & k4_t_5>=k4_t_4() & x_3=2*k4_t_5 + x_2() -> x_3>b".asFormula
  }

  it should "find solutions for x'=v if None is provided" in {
    val s = sequent(Nil, "x>0 & v()>=0".asFormula :: Nil, "[x'=v();]x>0".asFormula :: Nil)

    // solution = None -> Mathematica
    val tactic = locateSucc(diffSolution(None)) & debugT("After Diff Solution") & locateSucc(ImplyRightT) & arithmeticT

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  it should "find solutions for x'=v, v'=a if None is provided" in {
    val s = sequent(Nil, "x>0 & v>=0 & a()>0".asFormula :: Nil, "[x'=v, v'=a();]x>0".asFormula :: Nil)

    // solution = None -> Mathematica
    val tactic = locateSucc(diffSolution(None)) & debugT("After Diff Solution") & locateSucc(ImplyRightT) & arithmeticT

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  it should "not introduce time if already present" in {
    val s = sequent(Nil, "x>0".asFormula :: "t=0".asFormula :: Nil, "[x'=2, t'=1;]x>0".asFormula :: Nil)

    // solution = None -> Mathematica
    val tactic = locateSucc(diffSolution(None))
    val node = helper.runTactic(tactic, new RootNode(s))

    node.openGoals() should have size 1
    node.openGoals().flatMap(_.sequent.ante) should contain only (
      "x>0".asFormula,
      "t=0".asFormula,
      "x_2()=x".asFormula,
      "t_2()=t".asFormula
      )
    node.openGoals().flatMap(_.sequent.succ) should contain only "true & t_3>=t_2() & x_3=2*(t_3-t_2())+x_2() -> x_3>0".asFormula

    helper.runTactic(arithmeticT, node.openGoals().last) shouldBe 'closed
  }

  it should "preserve time evolution domain constraints when using Mathematica to find solution" in {
    val s = sequent(Nil, "x>0 & t=0".asFormula :: Nil, "[x'=2, t'=1 & t<=5;]x>0".asFormula :: Nil)

    // solution = None -> Mathematica
    val tactic = locateSucc(diffSolution(None))
    val node = helper.runTactic(tactic, new RootNode(s))

    node.openGoals() should have size 1
    node.openGoals().flatMap(_.sequent.ante) should contain only (
      "x>0 & t=0".asFormula,
      "x_2()=x".asFormula,
      "t_2()=t".asFormula
      )
    node.openGoals().flatMap(_.sequent.succ) should contain only "t_3<=5 & t_3>=t_2() & x_3=2*(t_3-t_2())+x_2() -> x_3>0".asFormula

    helper.runTactic(arithmeticT, node.openGoals().last) shouldBe 'closed
  }

  it should "work with evolution domain constraints" in {
    val s = sequent(Nil, "x>0 & v>=0".asFormula :: Nil, "[x'=v, v'=a() & v>=0;]x>0".asFormula :: Nil)

    // solution = None -> Mathematica
    val tactic = locateSucc(diffSolution(None)) & debugT("After Diff Solution") & arithmeticT

    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  "Differential auxiliaries tactic" should "add y'=1 to [x'=2]x>0" in {
    import ODETactics.diffAuxiliaryT
    val s = sucSequent("[x'=2;]x>0".asFormula)
    val tactic = locateSucc(diffAuxiliaryT(Variable("y", None, Real), "0".asTerm, "1".asTerm))
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("(x>0 <-> \\exists y. x>0) & [x'=2,y'=0*y+1;]x>0".asFormula)
    )
  }

  it should "add y'=3*y+10 to [x'=x+2*z]x>0" in {
    import ODETactics.diffAuxiliaryT
    val s = sucSequent("[x'=2;]x>0".asFormula)
    val tactic = locateSucc(diffAuxiliaryT(Variable("y", None, Real), "3".asTerm, "10".asTerm))
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("(x>0 <-> \\exists y. x>0) & [x'=2,y'=3*y+10;]x>0".asFormula)
    )
  }

  // TODO axiom does not know that z is constant in this concrete example
  ignore should "add y'=3*y+z to [x'=x+2*z]x>0" in {
    import ODETactics.diffAuxiliaryT
    val s = sucSequent("[x'=2;]x>0".asFormula)
    val tactic = locateSucc(diffAuxiliaryT(Variable("y", None, Real), "3".asTerm, "z".asTerm))
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("(x>0 <-> \\exists y. x>0) & [x'=2,y'=3*y+z;]x>0".asFormula)
    )
  }

  it should "use a provided safety predicate" in {
    import ODETactics.diffAuxiliaryT
    val s = sucSequent("[x'=2;]x>0".asFormula)
    val tactic = locateSucc(diffAuxiliaryT(Variable("y", None, Real), "3".asTerm, "10".asTerm, Some("y>2*x".asFormula)))
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("(x>0 <-> \\exists y. y>2*x) & [x'=2,y'=3*y+10;]y>2*x".asFormula)
    )
  }

  it should "preserve evolution domain" in {
    import ODETactics.diffAuxiliaryT
    val s = sucSequent("[x'=2 & x>=0;]x>0".asFormula)
    val tactic = locateSucc(diffAuxiliaryT(Variable("y", None, Real), "3".asTerm, "10".asTerm, Some("y>2*x".asFormula)))
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("(x>0 <-> \\exists y. y>2*x) & [x'=2,y'=3*y+10 & x>=0;]y>2*x".asFormula)
    )
  }

  it should "not allow non-linear ghosts (1)" in {
    import ODETactics.diffAuxiliaryT
    val s = sucSequent("[x'=2;]x>0".asFormula)
    val tactic = locateSucc(diffAuxiliaryT(Variable("y", None, Real), "y".asTerm, "1".asTerm))
    tactic.applicable(new RootNode(s)) shouldBe false
  }

  it should "not allow non-linear ghosts (2)" in {
    import ODETactics.diffAuxiliaryT
    val s = sucSequent("[x'=2;]x>0".asFormula)
    val tactic = locateSucc(diffAuxiliaryT(Variable("y", None, Real), "1".asTerm, "y".asTerm))
    tactic.applicable(new RootNode(s)) shouldBe false
  }

  it should "not allow ghosts that are already present in the ODE" in {
    import ODETactics.diffAuxiliaryT
    val s = sucSequent("[x'=2;]x>0".asFormula)
    val tactic = locateSucc(diffAuxiliaryT(Variable("x", None, Real), "0".asTerm, "1".asTerm))
    tactic.applicable(new RootNode(s)) shouldBe false
  }
}
