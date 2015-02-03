import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{Tactic, PositionTactic}
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{PrivateMethodTester, BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.StringConverter._
import testHelper.SequentFactory._
import testHelper.ProofFactory._

import scala.collection.immutable.Map

/**
 * Created by smitsch on 1/13/15.
 * @author Stefan Mitsch
 * @author Ran Ji
 */
class HybridProgramTacticTests extends FlatSpec with Matchers with BeforeAndAfterEach with PrivateMethodTester {
  Config.mathlicenses = 1
  Config.maxCPUs = 1

  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig : Map[String, String] = Map("linkName" -> "/Applications/Mathematica.app/Contents/MacOS/MathKernel")

  override def beforeEach() = {
    Tactics.MathematicaScheduler.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
  }

  "Box assignment equal tactic" should "introduce universal quantifier with new variable" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val assignT = locateSucc(boxAssignEqualT)
    getProofSequent(assignT, new RootNode(sucSequent("[y:=1;]y>0".asFormula))) should be (sucSequent("\\forall y_0. (y_0=1 -> y_0>0)".asFormula))
    getProofSequent(assignT, new RootNode(sucSequent("[y:=y+1;]y>0".asFormula))) should be (sucSequent("\\forall y_0. (y_0=y+1 -> y_0>0)".asFormula))
  }

  it should "replace free variables in predicate with new universally quantified variable" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val assignT = helper.positionTacticToTactic(boxAssignEqualT)
    getProofSequent(assignT, new RootNode(sucSequent("[y:=1;][z:=2;](y>0 & z>0)".asFormula))) should be (
      sucSequent("\\forall y_0. (y_0=1 -> [z:=2;](y_0>0 & z>0))".asFormula))
  }

  it should "not replace bound variables with new universally quantified variable" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val s = sucSequent("[y:=1;][y:=2;]y>0".asFormula)
    val assignT = helper.positionTacticToTactic(boxAssignEqualT)
    getProofSequent(assignT, new RootNode(s)) should be (
      sucSequent("\\forall y_0. (y_0=1 -> [y:=2;]y>0)".asFormula))
  }

  it should "only replace free but not bound variables with new universally quantified variable" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val s = sucSequent("[y:=1;][y:=2+y;]y>0".asFormula)
    val assignT = helper.positionTacticToTactic(boxAssignEqualT)
    getProofSequent(assignT, new RootNode(s)) should be (
      sucSequent("\\forall y_0. (y_0=1 -> [y:=2+y_0;]y>0)".asFormula))
    getProofSequent(assignT, new RootNode(sucSequent("[y:=1;][z:=2;](y>0 & z>0)".asFormula))) should be (
      sucSequent("\\forall y_0. (y_0=1 -> [z:=2;](y_0>0 & z>0))".asFormula))
    getProofSequent(assignT, new RootNode(sucSequent("[y:=1;][y:=2;]y>0".asFormula))) should be (
      sucSequent("\\forall y_0. (y_0=1 -> [y:=2;]y>0)".asFormula))
    getProofSequent(assignT, new RootNode(sucSequent("[y:=1;][y:=2+y;]y>0".asFormula))) should be (
      sucSequent("\\forall y_0. (y_0=1 -> [y:=2+y_0;]y>0)".asFormula))
  }

  it should "replace free variables in ODEs with new universally quantified variable" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val s = sucSequent("[y:=1;][z'=2+y;](y>0 & z>0)".asFormula)
    val assignT = helper.positionTacticToTactic(boxAssignEqualT)
    getProofSequent(assignT, new RootNode(s)) should be (
      sucSequent("\\forall y_0. (y_0=1 -> [z'=2+y_0;](y_0>0 & z>0))".asFormula))
  }

  it should "rebind original variable even if no other program follows" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val s = sucSequent("[y:=y+1;]y>0".asFormula)
    val assignT = helper.positionTacticToTactic(boxAssignEqualT)
    getProofSequent(assignT, new RootNode(s)) should be (
      sucSequent("\\forall y_0. (y_0=y+1 -> y_0>0)".asFormula))
  }

  it should "work in front of any discrete program" in {
    // TODO test all, but probably not in one shot
    import HybridProgramTacticsImpl.boxAssignEqualT
    import TacticLibrary.{skolemizeT, ImplyRightT}
    val s = sucSequent("[y:=z;][y:=2;][?y>1;]y>0".asFormula)
    val assignT = locateSucc(boxAssignEqualT) & locateSucc(skolemizeT) & locateSucc(ImplyRightT)

    val afterFirst = getProofGoals(assignT, new RootNode(s))
    getProofSequentFromGoals(afterFirst) should be (
      sequent("y_1".asNamedSymbol :: Nil, "y_1=z".asFormula :: Nil, "[y:=2;][?y>1;]y>0".asFormula :: Nil))

    getProofSequent(assignT, afterFirst) should be (
      sequent("y_1".asNamedSymbol :: "y_2".asNamedSymbol :: Nil,
        "y_1=z".asFormula :: "y_2=2".asFormula :: Nil,
        "[?y_2>1;]y_2>0".asFormula :: Nil))
  }

  it should "work in front of a loop" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val s = sucSequent("[x:=1;][{x:=x+1;}*;]x>0".asFormula)
    val assignT = locateSucc(boxAssignEqualT)
    getProofSequent(assignT, new RootNode(s)) should be (
      sucSequent("\\forall x_1. (x_1 = 1 -> [x_1:=x_1;][{x_1:=x_1+1;}*;]x_1>0)".asFormula))
  }

  it should "work in front of an ODE" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val s = sucSequent("[x:=1;][x'=1;]x>0".asFormula)
    val assignT = locateSucc(boxAssignEqualT)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall x_1. (x_1=1 -> [x_1:=x_1;][x_1'=1;]x_1>0)".asFormula)))
  }

  "Combined box assign tactics" should "handle assignment in front of an ODE" in {
    import TacticLibrary.boxAssignT
    val s = sucSequent("[x:=1;][x'=1;]x>0".asFormula)
    val assignT = locateSucc(boxAssignT)
    getProofSequent(assignT, new RootNode(s)) should be (
      sequent("x_2".asNamedSymbol :: Nil, "x_2=1".asFormula :: Nil, "[x_2'=1;]x_2>0".asFormula :: Nil))
  }

  it should "handle arbitrary assignments to variables not mentioned in subsequent formulas" in {
    import HybridProgramTacticsImpl.boxAssignT
    val tactic = locateSucc(boxAssignT)
    getProofSequent(tactic, new RootNode(sucSequent("[y_0:=y;][y'=2;]y>0".asFormula))) should be (
      sequent("y_2".asNamedSymbol :: Nil, "y_2=y".asFormula :: Nil, "[y'=2;]y>0".asFormula :: Nil))
  }

  it should "handle arbitrary assignments and not fail continuation" in {
    import HybridProgramTacticsImpl.boxAssignT
    val tactic = locateSucc(boxAssignT) & locateSucc(diffWeakenT)
    getProofSequent(tactic, new RootNode(sucSequent("[x_0:=x;][x'=2;]x>0".asFormula))) should be (
      sequent("x_2".asNamedSymbol :: "x_3".asNamedSymbol :: Nil, "x_2=x".asFormula :: "true".asFormula :: Nil,
        "x_3>0".asFormula :: Nil))
  }

  it should "handle assignment in front of a loop" in {
    import TacticLibrary.boxAssignT
    val s = sucSequent("[x:=1;][{x:=x+1;}*;]x>0".asFormula)
    val assignT = locateSucc(boxAssignT)
    getProofSequent(assignT, new RootNode(s)) should be (
      sequent("x_2".asNamedSymbol :: Nil, "x_2=1".asFormula :: Nil, "[{x_2:=x_2+1;}*;]x_2>0".asFormula :: Nil))
  }

  "v2tBoxAssignT" should "work on self assignment" in {
    val tacticFactory = PrivateMethod[PositionTactic]('v2tBoxAssignT)
    val assignT = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory())
    getProofSequent(assignT, new RootNode(sucSequent("[y:=y;]y>0".asFormula))) should be (sucSequent("y>0".asFormula))
    getProofSequent(assignT, new RootNode(sucSequent("[y:=y;][y:=2;]y>0".asFormula))) should be (sucSequent("[y:=2;]y>0".asFormula))
    getProofSequent(assignT, new RootNode(sucSequent("[y:=y;][{y:=y+1;}*;]y>0".asFormula))) should be (sucSequent("[{y:=y+1;}*;]y>0".asFormula))
  }

  it should "update self assignments" in {
    val tacticFactory = PrivateMethod[PositionTactic]('v2tBoxAssignT)
    val assignT = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory())
    getProofSequent(assignT, new RootNode(sucSequent("[y:=z;][y:=y;]y>0".asFormula))) should be (sucSequent("[y:=z;]y>0".asFormula))
  }

  ignore should "handle self assignments inside formulas" in {
    val tacticFactory = PrivateMethod[PositionTactic]('v2tBoxAssignT)
    val assignT = (HybridProgramTacticsImpl invokePrivate tacticFactory())(new SuccPosition(0, new PosInExpr(0 :: Nil)))
    // equivalence rewriting will not go past bound y in \\forall y
    getProofSequent(assignT, new RootNode(sucSequent("\\forall y. [y:=y;]y>0".asFormula))) should be (
      sucSequent("\\forall y. y>0".asFormula))
  }

  "Box test tactic" should "use axiom [?H;]p <-> (H->p)" in {
    import TacticLibrary.boxTestT
    val s = sucSequent("[?y>2;]y>0".asFormula)
    val tactic = locateSucc(boxTestT)
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("y>2 -> y>0".asFormula))
  }

  "Box nondeterministic assignment tactic" should "introduce universal quantifier and rename free variables" in {
    import TacticLibrary.boxNDetAssign
    val s = sucSequent("[y:=*;]y>0".asFormula)
    val tactic = locateSucc(boxNDetAssign)
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("\\forall y. y>0".asFormula))
  }

  it should "rename free variables in modality predicates" in {
    import TacticLibrary.boxNDetAssign
    val s = sucSequent("[y:=*;][z:=2;](y>0 & z>0)".asFormula)
    val assignT = locateSucc(boxNDetAssign)
    getProofSequent(assignT, new RootNode(s)) should be (
      sucSequent("\\forall y. [z:=2;](y>0 & z>0)".asFormula))
  }

  it should "rename free variables but not bound variables" in {
    import TacticLibrary.boxNDetAssign
    val s = sucSequent("[y:=*;][y:=2;]y>0".asFormula)
    val assignT = locateSucc(boxNDetAssign)
    getProofSequent(assignT, new RootNode(s)) should be (
      sucSequent("\\forall y. [y:=2;]y>0".asFormula))
  }

  it should "rename free variables but not variables bound by assignment in modality predicates" in {
    import TacticLibrary.boxNDetAssign
    val s = sucSequent("[y:=*;][y:=2+y;]y>0".asFormula)
    val assignT = locateSucc(boxNDetAssign)
    getProofSequent(assignT, new RootNode(s)) should be (
      sucSequent("\\forall y. [y:=2+y;]y>0".asFormula))
  }

  it should "rename free variables but not variables bound by ODEs in modality predicates" in {
    import TacticLibrary.boxNDetAssign
    val s = sucSequent("[y:=*;][z'=2+y;](y>0 & z>0)".asFormula)
    val assignT = locateSucc(boxNDetAssign)
    getProofSequent(assignT, new RootNode(s)) should be (
      sucSequent("\\forall y. [z'=2+y;](y>0 & z>0)".asFormula))
  }

  it should "work in front of any discrete program" in {
    // TODO test all, but probably not in one shot
    import TacticLibrary.{boxNDetAssign, skolemizeT, ImplyRightT}
    val s = sucSequent("[y:=*;][y:=*;][?y>1;]y>0".asFormula)
    val assignT = locateSucc(boxNDetAssign) & debugT("ndet") & locateSucc(skolemizeT) & locateSucc(ImplyRightT)

    val afterFirst = getProofGoals(assignT, new RootNode(s))
    getProofSequentFromGoals(afterFirst) should be (
      sequent("y_0".asNamedSymbol :: Nil, Nil, "[y_0:=*;][?y_0>1;]y_0>0".asFormula :: Nil))

    val afterSecond = getProofGoals(assignT, afterFirst)
    getProofSequentFromGoals(afterSecond) should be (
      sequent("y_0".asNamedSymbol :: "y_1".asNamedSymbol :: Nil, Nil, "[?y_1>1;]y_1>0".asFormula :: Nil))
  }

  it should "work in front of a loop" in {
    val s = sucSequent("[y:=*;][{y:=y+2;}*;]y>0".asFormula)
    val assignT = locateSucc(boxNDetAssign) & locateSucc(skolemizeT) & locateSucc(ImplyRightT)
    getProofSequent(assignT, new RootNode(s)) should be (
      sequent("y_0".asNamedSymbol :: Nil, Nil, "[{y_0:=y_0+2;}*;]y_0>0".asFormula :: Nil))
  }

  it should "work in front of a continuous program" in {
    val s = sucSequent("[y:=*;][y'=2;]y>0".asFormula)
    val assignT = locateSucc(boxNDetAssign)
    getProofSequent(assignT, new RootNode(s)) should be (
      sequent("y_2".asNamedSymbol :: Nil, Nil, "[y_2'=2;]y_2>0".asFormula :: Nil))
  }

  "v2tBoxAssignT" should "replace with variables" in {
    val s = sucSequent("[y:=z;]y>0".asFormula)
    val tacticFactory = PrivateMethod[PositionTactic]('v2tBoxAssignT)
    val assignT = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory())
    getProofSequent(assignT, new RootNode(s)) should be (
      sucSequent("z>0".asFormula))
  }

  it should "work with arbitrary terms" in {
    val s = sucSequent("[y:=1;][y:=y;]y>0".asFormula)
    val tacticFactory = PrivateMethod[PositionTactic]('v2tBoxAssignT)
    val assignT = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory())
    getProofSequent(assignT, new RootNode(s)) should be (sucSequent("[y:=1;]y>0".asFormula))
  }

  it should "not apply when immediately followed by an ODE or loop" in {
    val tacticFactory = PrivateMethod[PositionTactic]('v2tBoxAssignT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory())
    an [Exception] should be thrownBy
      getProofSequent(tactic, new RootNode(sucSequent("[y:=z;][y'=z+1;]y>0".asFormula)))
    an [Exception] should be thrownBy
      getProofSequent(tactic, new RootNode(sucSequent("[y:=z;][{y:=z+1;}*]y>0".asFormula)))
  }

  "v2vBoxAssignT" should "work on ODEs" in {
    import HybridProgramTacticsImpl.v2vBoxAssignT
    val tactic = locateSucc(v2vBoxAssignT)
    getProofSequent(tactic, new RootNode(sucSequent("[y:=z;][y'=2;]y>0".asFormula))) should be (sucSequent("[z'=2;]z>0".asFormula))
  }

  it should "not apply when the replacement is not free in ODEs or loops" in {
    import HybridProgramTacticsImpl.v2vBoxAssignT
    val tactic = locateSucc(v2vBoxAssignT)
    the [Exception] thrownBy
      getProofSequent(tactic, new RootNode(sucSequent("[y:=z;][y'=z+1;]y>0".asFormula))) should have message "runTactic was called on tactic Position tactic locateSucc ([:=] assignment)([:=] assignment), but is not applicable on the node."
  }

  it should "work in the antecedent" in {
    import HybridProgramTacticsImpl.v2vBoxAssignT
    val tactic = locateAnte(v2vBoxAssignT)
    getProofSequent(tactic, new RootNode(sequent(Nil, "[y:=z;][y'=2;]y>0".asFormula :: Nil, Nil))) should be (
      sequent(Nil, "[z'=2;]z>0".asFormula :: Nil, Nil))
  }


  it should "work on loops" in {
    val s = sucSequent("[y:=z;][{y:=y+2;}*;]y>0".asFormula)
    import HybridProgramTacticsImpl.v2vBoxAssignT
    val tactic = locateSucc(v2vBoxAssignT)
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("[{z:=z+2;}*;]z>0".asFormula))
  }

  "Discrete ghost" should "introduce assignment to fresh variable" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(None, new Variable("y", None, Real)))

    getProofSequent(tactic, new RootNode(sucSequent("y>0".asFormula))) should be (
      sucSequent("[y_0:=y;]y_0>0".asFormula))
  }

  it should "assign term t to fresh variable" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(Some(new Variable("z", None, Real)),
      "y+1".asTerm))
    getProofSequent(tactic, new RootNode(sucSequent("y+1>0".asFormula))) should be (
      sucSequent("[z:=y+1;]z>0".asFormula))
  }

  it should "allow arbitrary terms t when a ghost name is specified" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(Some(Variable("z", None, Real)),
      "x+5".asTerm))
    getProofSequent(tactic, new RootNode(sucSequent("y>0".asFormula))) should be (
      sucSequent("[z:=x+5;]y>0".asFormula))
  }

  it should "not allow arbitrary terms t when no ghost name is specified" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(None, "x+5".asTerm))
    // would like to expect exception, but cannot because of Scheduler
    getProofSequent(tactic, new RootNode(sucSequent("y>0".asFormula))) should be (
      sucSequent("y>0".asFormula))
  }

  it should "use same variable if asked to do so" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(Some(new Variable("y", None, Real)),
      new Variable("y", None, Real)))
    getProofSequent(tactic, new RootNode(sucSequent("y>0".asFormula))) should be (
      sucSequent("[y:=y;]y>0".asFormula))
  }

  it should "use specified fresh variable" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(Some(new Variable("z", None, Real)),
      new Variable("y", None, Real)))
    getProofSequent(tactic, new RootNode(sucSequent("y>0".asFormula))) should be (
      sucSequent("[z:=y;]z>0".asFormula))
  }

  it should "not accept variables present in f" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(Some(new Variable("z", None, Real)),
      new Variable("y", None, Real)))
    // would like to test, but cannot because of Scheduler
    //    an [IllegalArgumentException] should be thrownBy
    //      helper.runTactic(tactic, new RootNode(sucSequent("y>z+1".asFormula)))
    getProofSequent(tactic, new RootNode(sucSequent("y>z+1".asFormula))) should be (
      sucSequent("y>z+1".asFormula))
  }

  it should "work on assignments" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(None, Variable("y", None, Real)))
    getProofSequent(tactic, new RootNode(sucSequent("[y:=2;]y>0".asFormula))) should be (
      sucSequent("[y_0:=y;][y:=2;]y>0".asFormula))
  }

  it should "introduce ghosts in the middle of formulas" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = (HybridProgramTacticsImpl invokePrivate tacticFactory(None, Variable("y", None, Real)))(
      new SuccPosition(0, new PosInExpr(1 :: Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("[x:=1;][y:=2;]y>0".asFormula))) should be (
      sucSequent("[x:=1;][y_0:=y;][y:=2;]y>0".asFormula))
  }

  it should "introduce self-assignment ghosts in the middle of formulas when not bound before" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = (HybridProgramTacticsImpl invokePrivate tacticFactory(Some(Variable("y", None, Real)), Variable("y", None, Real)))(new SuccPosition(0, new PosInExpr(1 :: Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("[x:=1;][y:=2;]y>0".asFormula))) should be (
      sucSequent("[x:=1;][y:=y;][y:=2;]y>0".asFormula))
  }

  it should "not introduce self-assignment ghosts in the middle of formulas when bound" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = (HybridProgramTacticsImpl invokePrivate tacticFactory(Some(Variable("y", None, Real)), Variable("y", None, Real)))(new SuccPosition(0, new PosInExpr(1 :: Nil)))
    // equivelance rewriting fails because x bound by x:=x+1
    getProofSequent(tactic, new RootNode(sucSequent("[x:=x+1;][x'=2;]x>0".asFormula))) should be (
      sequent(Nil, "[y:=y;][x'=2;]x>0 <-> [x'=2;]x>0".asFormula :: Nil, "[x:=x+1;][x'=2;]x>0".asFormula :: Nil))
  }

  ignore should "introduce ghosts in modality predicates" in {
    // will not work because y is bound by y:=2, so equality rewriting does not work
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = (HybridProgramTacticsImpl invokePrivate tacticFactory(None, Variable("y", None, Real)))(new SuccPosition(0, new PosInExpr(1 :: Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("[y:=2;]y>0".asFormula))) should be (
      sucSequent("[y:=2;][y_0:=y;]y>0".asFormula))
  }

  it should "work on loops" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(None, Variable("y", None, Real)))
    getProofSequent(tactic, new RootNode(sucSequent("[{y:=y+1;}*;]y>0".asFormula))) should be (
      sucSequent("[y_0:=y;][{y:=y+1;}*;]y>0".asFormula))
  }

  it should "work on ODEs" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(None, Variable("y", None, Real)))
    getProofSequent(tactic, new RootNode(sucSequent("[y'=1;]y>0".asFormula))) should be (
      sucSequent("[y_0:=y;][y'=1;]y>0".asFormula))
  }

  ignore should "introduce self-assignment in front of ODEs" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(Some("y".asNamedSymbol), "y".asTerm))
    // substitution clash because y is getting bound by assignment
    getProofSequent(tactic, new RootNode(sucSequent("[y'=1;]y>0".asFormula))) should be (
      sucSequent("[y:=y;][y'=1;]y>0".asFormula))
  }

  it should "not propagate arbitrary terms into ODEs" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(Some(Variable("z", None, Real)),
      "y+1".asTerm))
    // would like to check for exception, but not possible because of Scheduler
    getProofSequent(tactic, new RootNode(sucSequent("[y'=1;]y>0".asFormula))) should be (
      sucSequent("[z:=y+1;][y'=1;]y>0".asFormula))
  }
}
