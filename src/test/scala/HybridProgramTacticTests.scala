import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.Tactics.PositionTactic
import edu.cmu.cs.ls.keymaera.tactics.{HybridProgramTacticsImpl, TacticLibrary, Config, Tactics}
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{PrivateMethodTester, BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.StringConverter._
import testHelper.SequentFactory._

import scala.collection.immutable.Map

/**
 * Created by smitsch on 1/13/15.
 * @author Stefan Mitsch
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

  "Box assignment tactic" should "introduce universal quantifier with new variable" in {
    import TacticLibrary.boxAssignT
    val assignT = locateSucc(boxAssignT)
    helper.runTactic(assignT, new RootNode(sucSequent("[y:=1;]y>0".asFormula))).openGoals()
      .foreach(_.sequent should be (sucSequent("\\forall y_0. (y_0=1 -> y_0>0)".asFormula)))
    helper.runTactic(assignT, new RootNode(sucSequent("[y:=y+1;]y>0".asFormula))).openGoals()
      .foreach(_.sequent should be (sucSequent("\\forall y_0. (y_0=y+1 -> y_0>0)".asFormula)))
  }

  it should "replace free variables in predicate with new universally quantified variable" in {
    import TacticLibrary.boxAssignT
    val s = sucSequent("[y:=1;][z:=2;](y>0 & z>0)".asFormula)
    val assignT = helper.positionTacticToTactic(boxAssignT)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall y_0. (y_0=1 -> [z:=2;](y_0>0 & z>0))".asFormula)))
  }

  it should "even replace bound variables with new universally quantified variable" in {
    import TacticLibrary.boxAssignT
    val s = sucSequent("[y:=1;][y:=2;]y>0".asFormula)
    val assignT = helper.positionTacticToTactic(boxAssignT)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall y_0. (y_0=1 -> [y_0:=2;]y_0>0)".asFormula)))
  }

  it should "only replace free but not bound variables with new universally quantified variable" in {
    import TacticLibrary.boxAssignT
    val s = sucSequent("[y:=1;][y:=2+y;]y>0".asFormula)
    val assignT = helper.positionTacticToTactic(boxAssignT)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall y_0. (y_0=1 -> [y_0:=2+y_0;]y_0>0)".asFormula)))
  }

  it should "replace free variables in ODEs with new universally quantified variable" in {
    import TacticLibrary.boxAssignT
    val s = sucSequent("[y:=1;][z'=2+y;](y>0 & z>0)".asFormula)
    val assignT = helper.positionTacticToTactic(boxAssignT)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall y_0. (y_0=1 -> [z'=2+y_0;](y_0>0 & z>0))".asFormula)))
  }

  it should "rebind original variable even if no other program follows" in {
    import TacticLibrary.boxAssignT
    val s = sucSequent("[y:=y+1;]y>0".asFormula)
    val assignT = helper.positionTacticToTactic(boxAssignT)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall y_0. (y_0=y+1 -> y_0>0)".asFormula)))
  }

  it should "work in front of any discrete program" in {
    // TODO test all, but probably not in one shot
    import TacticLibrary.{boxAssignT, skolemizeT, ImplyRightT}
    val s = sucSequent("[y:=z;][y:=2;][?y>1;]y>0".asFormula)
    val assignT = locateSucc(boxAssignT) & locateSucc(skolemizeT) & locateSucc(ImplyRightT)
    val afterFirst = helper.runTactic(assignT, new RootNode(s))
    afterFirst.openGoals().foreach(_.sequent should be (
      sequent("y_1".asNamedSymbol :: Nil, "y_1=z".asFormula :: Nil, "[y_1:=2;][?y_1>1;]y_1>0".asFormula :: Nil)))

    val afterSecond = helper.runTactic(assignT, afterFirst.openGoals().head)
    afterSecond.openGoals().foreach(_.sequent should be (
      sequent("y_1".asNamedSymbol :: "y_3".asNamedSymbol :: Nil,
        "y_1=z".asFormula :: "y_3=2".asFormula :: Nil,
        "[?y_3>1;]y_3>0".asFormula :: Nil)))
  }

  it should "work in front of a loop" in {
    import TacticLibrary.{boxAssignT, locateSucc, skolemizeT}
    val s = sucSequent("[x:=1;][{x:=x+1;}*;]x>0".asFormula)
    val assignT = locateSucc(boxAssignT) & locateSucc(skolemizeT) & locateSucc(ImplyRightT)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent("x_1".asNamedSymbol :: Nil, "x_1=1".asFormula :: Nil, "[{x_1:=x_1+1;}*;]x_1>0".asFormula :: Nil)))
  }

  it should "work in front of an ODE" in {
    import TacticLibrary.{boxAssignT, locateSucc, skolemizeT}
    val s = sucSequent("[x:=1;][x'=1;]x>0".asFormula)
    val tacticFactory = PrivateMethod[PositionTactic]('predicateReplaceBoxAssignT)
    val assignT = locateSucc(boxAssignT) & locateSucc(skolemizeT) & locateSucc(ImplyRightT) &
      locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory())
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent("x_1".asNamedSymbol :: Nil, "x_1=1".asFormula :: Nil, "[x_1'=1;]x_1>0".asFormula :: Nil)))
  }

  "Box test tactic" should "use axiom [?H;]p <-> (H->p)" in {
    import TacticLibrary.boxTestT
    val s = sucSequent("[?y>2;]y>0".asFormula)
    val tactic = locateSucc(boxTestT)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("y>2 -> y>0".asFormula)))
  }

  "Box nondeterministic assignment tactic" should "introduce universal quantifier and rename free variables" in {
    import TacticLibrary.boxNDetAssign
    val s = sucSequent("[y:=*;]y>0".asFormula)
    val tactic = locateSucc(boxNDetAssign)
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall y. y>0".asFormula)))
  }

  it should "rename free variables in modality predicates" in {
    import TacticLibrary.boxNDetAssign
    val s = sucSequent("[y:=*;][z:=2;](y>0 & z>0)".asFormula)
    val assignT = locateSucc(boxNDetAssign)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall y. [z:=2;](y>0 & z>0)".asFormula)))
  }

  it should "rename free variables but not bound variables" in {
    import TacticLibrary.boxNDetAssign
    val s = sucSequent("[y:=*;][y:=2;]y>0".asFormula)
    val assignT = locateSucc(boxNDetAssign)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall y. [y:=2;]y>0".asFormula)))
  }

  it should "rename free variables but not variables bound by assignment in modality predicates" in {
    import TacticLibrary.boxNDetAssign
    val s = sucSequent("[y:=*;][y:=2+y;]y>0".asFormula)
    val assignT = locateSucc(boxNDetAssign)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall y. [y:=2+y;]y>0".asFormula)))
  }

  it should "rename free variables but not variables bound by ODEs in modality predicates" in {
    import TacticLibrary.boxNDetAssign
    val s = sucSequent("[y:=*;][z'=2+y;](y>0 & z>0)".asFormula)
    val assignT = locateSucc(boxNDetAssign)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall y. [z'=2+y;](y>0 & z>0)".asFormula)))
  }

  it should "work in front of any discrete program" in {
    // TODO test all, but probably not in one shot
    import TacticLibrary.{boxNDetAssign, skolemizeT, ImplyRightT}
    val s = sucSequent("[y:=*;][y:=*;][?y>1;]y>0".asFormula)
    val assignT = locateSucc(boxNDetAssign) & locateSucc(skolemizeT) & locateSucc(ImplyRightT)
    val afterFirst = helper.runTactic(assignT, new RootNode(s))
    afterFirst.openGoals().foreach(_.sequent should be (
      sequent("y_0".asNamedSymbol :: Nil, Nil, "[y_0:=*;][?y_0>1;]y_0>0".asFormula :: Nil)))

    val afterSecond = helper.runTactic(assignT, afterFirst.openGoals().head)
    afterSecond.openGoals().foreach(_.sequent should be (
      sequent("y_0".asNamedSymbol :: "y_1".asNamedSymbol :: Nil, Nil, "[?y_1>1;]y_1>0".asFormula :: Nil)))
  }

  it should "work in front of a loop" in {
    val s = sucSequent("[y:=*;][{y:=y+2;}*;]y>0".asFormula)
    val assignT = locateSucc(boxNDetAssign) & locateSucc(skolemizeT) & locateSucc(ImplyRightT)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent("y_0".asNamedSymbol :: Nil, Nil, "[{y_0:=y_0+2;}*;]y_0>0".asFormula :: Nil)))
  }

  it should "work in front of a continuous program" in {
    val s = sucSequent("[y:=*;][y'=2;]y>0".asFormula)
    val assignT = locateSucc(boxNDetAssign) & locateSucc(skolemizeT) & locateSucc(ImplyRightT)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent("y_0".asNamedSymbol :: Nil, Nil, "[y_0'=2;]y_0>0".asFormula :: Nil)))
  }

  "Predicate replace box assignment" should "replace with variables" in {
    val s = sucSequent("[y:=z;]y>0".asFormula)
    val tacticFactory = PrivateMethod[PositionTactic]('predicateReplaceBoxAssignT)
    val assignT = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory())
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("z>0".asFormula)))
  }

  it should "work on self assignment" in {
    val tacticFactory = PrivateMethod[PositionTactic]('predicateReplaceBoxAssignT)
    val assignT = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory())
    helper.runTactic(assignT, new RootNode(sucSequent("[y:=y;]y>0".asFormula)))
      .openGoals().foreach(_.sequent should be (sucSequent("y>0".asFormula)))
    helper.runTactic(assignT, new RootNode(sucSequent("[y:=y;][y:=2;]y>0".asFormula)))
      .openGoals().foreach(_.sequent should be (sucSequent("[y:=2;]y>0".asFormula)))
    helper.runTactic(assignT, new RootNode(sucSequent("[y:=y;][{y:=y+1;}*;]y>0".asFormula)))
      .openGoals().foreach(_.sequent should be (sucSequent("[{y:=y+1;}*;]y>0".asFormula)))
  }

  it should "update self assignments" in {
    import HybridProgramTacticsImpl.predicateReplaceBoxAssignT
    val s = sucSequent("[y:=z;][y:=y;]y>0".asFormula)
    val tacticFactory = PrivateMethod[PositionTactic]('predicateReplaceBoxAssignT)
    val assignT = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory())
    helper.runTactic(assignT, new RootNode(sequent(Nil, Nil, "[y:=y;]y>0".asFormula :: Nil)))
      .openGoals().foreach(_.sequent should be (sequent(Nil, Nil, "y>0".asFormula :: Nil)))
    helper.runTactic(assignT, new RootNode(sequent(Nil, Nil, "[y:=y;][y:=2;]y>0".asFormula :: Nil)))
      .openGoals().foreach(_.sequent should be (sequent(Nil, Nil, "[y:=2;]y>0".asFormula :: Nil)))
    helper.runTactic(assignT, new RootNode(sequent(Nil, Nil, "[y:=y;][{y:=y+1;}*;]y>0".asFormula :: Nil)))
      .openGoals().foreach(_.sequent should be (sequent(Nil, Nil, "[{y:=y+1;}*;]y>0".asFormula :: Nil)))
  }

  it should "update self assignments" in {
    val s = sequent(Nil, Nil, "[y:=z;][y:=y;]y>0".asFormula :: Nil)
    val tacticFactory = PrivateMethod[PositionTactic]('predicateReplaceBoxAssignT)
    val assignT = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory())
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[z:=z;]z>0".asFormula)))
  }

  ignore should "work with arbitrary terms" in {
    val s = sucSequent("[y:=1;][y:=y;]y>0".asFormula)
    val tacticFactory = PrivateMethod[PositionTactic]('predicateReplaceBoxAssignT)
    val assignT = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory())
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[y:=1;]y>0".asFormula)))
  }

  it should "work on ODEs" in {
    val s = sucSequent("[y:=z;][y'=2;]y>0".asFormula)
    val tacticFactory = PrivateMethod[PositionTactic]('predicateReplaceBoxAssignT)
    val assignT = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory())
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[z'=2;]z>0".asFormula)))
  }

  it should "work on loops" in {
    val s = sucSequent("[y:=z;][{y:=y+2;}*;]y>0".asFormula)
    val tacticFactory = PrivateMethod[PositionTactic]('predicateReplaceBoxAssignT)
    val assignT = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory())
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("[{z:=z+2;}*;]z>0".asFormula)))
  }

  "Discrete ghost" should "introduce assignment to fresh variable" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(None, new Variable("y", None, Real)))
    val node = helper.runTactic(tactic, new RootNode(sucSequent("y>0".asFormula)))
    node.openGoals().foreach(_.sequent should be (
      sucSequent("[y_0:=y;]y_0>0".asFormula)))
  }

  ignore should "assign term t to fresh variable" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(Some(new Variable("z", None, Real)),
      "y+1".asTerm))
    val node = helper.runTactic(tactic, new RootNode(sucSequent("y+1>0".asFormula)))
    node.openGoals().foreach(_.sequent should be (
      sucSequent("[z:=y+1;]z>0".asFormula)))
  }

  ignore should "allow allow arbitrary terms t when a ghost name is specified" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(Some(Variable("z", None, Real)),
      "x+5".asTerm))
    var node = helper.runTactic(tactic, new RootNode(sucSequent("y>0".asFormula)))
    // would like to expect exception, but cannot because of Scheduler
    node.openGoals().foreach(_.sequent should be (
      sucSequent("[z:=x+5;]y>0".asFormula)))
  }

  it should "not allow arbitrary terms t when no ghost name is specified" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(None, "x+5".asTerm))
    var node = helper.runTactic(tactic, new RootNode(sucSequent("y>0".asFormula)))
    // would like to expect exception, but cannot because of Scheduler
    node.openGoals().foreach(_.sequent should be (
      sucSequent("y>0".asFormula)))
  }

  it should "use same variable if asked to do so" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(Some(new Variable("y", None, Real)),
      new Variable("y", None, Real)))
    val node = helper.runTactic(tactic, new RootNode(sucSequent("y>0".asFormula)))
    node.openGoals().foreach(_.sequent should be (
      sucSequent("[y:=y;]y>0".asFormula)))
  }

  it should "use specified fresh variable" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(Some(new Variable("z", None, Real)),
      new Variable("y", None, Real)))
    val node = helper.runTactic(tactic, new RootNode(sucSequent("y>0".asFormula)))
    node.openGoals().foreach(_.sequent should be (
      sucSequent("[z:=y;]z>0".asFormula)))
  }

  it should "not accept variables present in f" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(Some(new Variable("z", None, Real)),
      new Variable("y", None, Real)))
    // would like to test, but cannot because of Scheduler
//    an [IllegalArgumentException] should be thrownBy
//      helper.runTactic(tactic, new RootNode(sucSequent("y>z+1".asFormula)))
    val node = helper.runTactic(tactic, new RootNode(sucSequent("y>z+1".asFormula)))
    node.openGoals().foreach(_.sequent should be (
      sucSequent("y>z+1".asFormula)))
  }

  it should "work on assignments" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(None, Variable("y", None, Real)))
    val node = helper.runTactic(tactic, new RootNode(sucSequent("[y:=2;]y>0".asFormula)))
    node.openGoals().foreach(_.sequent should be (
      sucSequent("[y_0:=y;][y:=2;]y>0".asFormula)))
  }

  // Do we really want to support this?
  ignore should "introduce ghosts in the middle of formulas" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = (HybridProgramTacticsImpl invokePrivate tacticFactory(None, Variable("y", None, Real)))(new SuccPosition(0, new PosInExpr(1 :: Nil)))
    val node = helper.runTactic(tactic, new RootNode(sucSequent("[x:=1;][y:=2;]y>0".asFormula)))
    node.openGoals().foreach(_.sequent should be (
      sucSequent("[x:=1;][y_0:=y;][y:=2;]y>0".asFormula)))
  }

  ignore should "introduce ghosts in modality predicates" in {
    // will not work because y is bound by y:=2, so equalityrewriting does not work
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = (HybridProgramTacticsImpl invokePrivate tacticFactory(None, Variable("y", None, Real)))(new SuccPosition(0, new PosInExpr(1 :: Nil)))
    val node = helper.runTactic(tactic, new RootNode(sucSequent("[y:=2;]y>0".asFormula)))
    node.openGoals().foreach(_.sequent should be (
      sucSequent("[y:=2;][y_0:=y;]y>0".asFormula)))
  }

  it should "work on loops" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(None, Variable("y", None, Real)))
    val node = helper.runTactic(tactic, new RootNode(sucSequent("[{y:=y+1;}*;]y>0".asFormula)))
    node.openGoals().foreach(_.sequent should be (
      sucSequent("[y_0:=y;][{y:=y+1;}*;]y>0".asFormula)))
  }

  it should "work on ODEs" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(None, Variable("y", None, Real)))
    val node = helper.runTactic(tactic, new RootNode(sucSequent("[y'=1;]y>0".asFormula)))
    node.openGoals().foreach(_.sequent should be (
      sucSequent("[y_0:=y;][y'=1;]y>0".asFormula)))
  }

  ignore should "not propagate arbitrary terms into ODEs" in {
    val tacticFactory = PrivateMethod[PositionTactic]('discreteGhostT)
    val tactic = locateSucc(HybridProgramTacticsImpl invokePrivate tacticFactory(Some(Variable("z", None, Real)),
      "y+1".asTerm))
    val node = helper.runTactic(tactic, new RootNode(sucSequent("[y'=1;]y>0".asFormula)))
    // would like to check for exception, but not possible because of Scheduler
    node.openGoals().foreach(_.sequent should be (
      sucSequent("[z:=y+1;][y'=1;]y>0".asFormula)))
  }
}
