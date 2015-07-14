import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl._
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.{locateSucc, locateAnte}
import edu.cmu.cs.ls.keymaerax.tactics.ODETactics.diffWeakenT
import edu.cmu.cs.ls.keymaerax.tactics.HybridProgramTacticsImpl.boxNDetAssign
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.{debugT, skolemizeT, ImplyRightT}
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.PositionTactic
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tools.{Mathematica, KeYmaera}
import testHelper.ProvabilityTestHelper
import org.scalatest.{PrivateMethodTester, BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.SequentFactory._
import testHelper.ProofFactory._

import scala.collection.immutable.Map
import scala.language.postfixOps

/**
 * Created by smitsch on 1/13/15.
 * @author Stefan Mitsch
 * @author Ran Ji
 */
class HybridProgramTacticTests extends FlatSpec with Matchers with BeforeAndAfterEach with PrivateMethodTester {
  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig: Map[String, String] = helper.mathematicaConfig

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
    Tactics.MathematicaScheduler.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    Tactics.MathematicaScheduler.shutdown()
    Tactics.KeYmaeraScheduler.shutdown()
    Tactics.KeYmaeraScheduler = null
    Tactics.MathematicaScheduler = null
  }

  "Box assignment equal tactic" should "introduce universal quantifier with new variable" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val assignT = locateSucc(boxAssignEqualT)
    getProofSequent(assignT, new RootNode(sucSequent("[y:=1;]y>0".asFormula))) should be (sucSequent("\\forall y_0 (y_0=1 -> y_0>0)".asFormula))
    getProofSequent(assignT, new RootNode(sucSequent("[y:=y+1;]y>0".asFormula))) should be (sucSequent("\\forall y_0 (y_0=y+1 -> y_0>0)".asFormula))
  }

  it should "replace free variables in predicate with new universally quantified variable" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val assignT = helper.positionTacticToTactic(boxAssignEqualT)
    getProofSequent(assignT, new RootNode(sucSequent("[y:=1;][z:=2;](y>0 & z>0)".asFormula))) should be (
      sucSequent("\\forall y_0 (y_0=1 -> [z:=2;](y_0>0 & z>0))".asFormula))
  }

  it should "not replace bound variables with new universally quantified variable" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val s = sucSequent("[y:=1;][y:=2;]y>0".asFormula)
    val assignT = helper.positionTacticToTactic(boxAssignEqualT)
    getProofSequent(assignT, new RootNode(s)) should be (
      sucSequent("\\forall y_0 (y_0=1 -> [y:=2;]y>0)".asFormula))
  }

  it should "only replace free but not bound variables with new universally quantified variable" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val s = sucSequent("[y:=1;][y:=2+y;]y>0".asFormula)
    val assignT = helper.positionTacticToTactic(boxAssignEqualT)
    getProofSequent(assignT, new RootNode(s)) should be (
      sucSequent("\\forall y_0 (y_0=1 -> [y:=2+y_0;]y>0)".asFormula))
    getProofSequent(assignT, new RootNode(sucSequent("[y:=1;][z:=2;](y>0 & z>0)".asFormula))) should be (
      sucSequent("\\forall y_0 (y_0=1 -> [z:=2;](y_0>0 & z>0))".asFormula))
    getProofSequent(assignT, new RootNode(sucSequent("[y:=1;][y:=2;]y>0".asFormula))) should be (
      sucSequent("\\forall y_0 (y_0=1 -> [y:=2;]y>0)".asFormula))
    getProofSequent(assignT, new RootNode(sucSequent("[y:=1;][y:=2+y;]y>0".asFormula))) should be (
      sucSequent("\\forall y_0 (y_0=1 -> [y:=2+y_0;]y>0)".asFormula))
  }

  it should "replace free variables in ODEs with new universally quantified variable" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val s = sucSequent("[y:=1;][{z'=2+y}](y>0 & z>0)".asFormula)
    val assignT = helper.positionTacticToTactic(boxAssignEqualT)
    getProofSequent(assignT, new RootNode(s)) should be (
      sucSequent("\\forall y_0 (y_0=1 -> [{z'=2+y_0}](y_0>0 & z>0))".asFormula))
  }

  it should "rebind original variable even if no other program follows" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val s = sucSequent("[y:=y+1;]y>0".asFormula)
    val assignT = helper.positionTacticToTactic(boxAssignEqualT)
    getProofSequent(assignT, new RootNode(s)) should be (
      sucSequent("\\forall y_0 (y_0=y+1 -> y_0>0)".asFormula))
  }

  it should "work in front of an ODE, even if it is not top-level" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val s = sucSequent("[x:=1;][t:=0; {x'=1}]x>0".asFormula)
    val assignT = locateSucc(boxAssignEqualT)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall x_1 (x_1=1 -> [x_0:=x_1;][t:=0;{x_0'=1}]x_0>0)".asFormula)))
  }

  it should "work in front of an ODE system, even if it is not top-level" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val s = sucSequent("[x:=1;][t:=0; {x'=1,y'=2}]x>0".asFormula)
    val assignT = locateSucc(boxAssignEqualT)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall x_1 (x_1=1 -> [x_0:=x_1;][t:=0;{x_0'=1,y'=2}]x_0>0)".asFormula)))
  }

  it should "work in front of an ODE, even if it is not in the next box" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val s = sucSequent("[x:=1;][t:=0;][t:=1; {x'=1}]x>0".asFormula)
    val assignT = locateSucc(boxAssignEqualT)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall x_1 (x_1=1 -> [x_0:=x_1;][t:=0;][t:=1; {x_0'=1}]x_0>0)".asFormula)))
  }

  it should "not introduce stuttering when ODE does not write variable, even if it is not top-level" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val s = sucSequent("[x:=1;][t:=0; {y'=1} {z:=2;}* ]x>0".asFormula)
    val assignT = locateSucc(boxAssignEqualT)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall x_0 (x_0=1 -> [t:=0;{y'=1}{z:=2;}*]x_0>0)".asFormula)))
  }

  it should "work in front of any discrete program" in {
    // TODO test all, but probably not in one shot
    import HybridProgramTacticsImpl.boxAssignEqualT
    import TacticLibrary.{skolemizeT, ImplyRightT}
    val s = sucSequent("[y:=z;][y:=2;][?y>1;]y>0".asFormula)
    val assignT = locateSucc(boxAssignEqualT) & locateSucc(skolemizeT) & locateSucc(ImplyRightT)

    val afterFirst = helper.runTactic(assignT, new RootNode(s))
    afterFirst.openGoals() should have size 1
    afterFirst.openGoals().flatMap(_.sequent.ante) should contain only "y_0=z".asFormula
    afterFirst.openGoals().flatMap(_.sequent.succ) should contain only "[y:=2;][?y>1;]y>0".asFormula

    val result = helper.runTactic(assignT, afterFirst.openGoals()(0))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only ("y_0=z".asFormula, "y_1=2".asFormula)
    result.openGoals().flatMap(_.sequent.succ) should contain only "[?y_1>1;]y_1>0".asFormula
  }

  it should "work in front of a loop" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val s = sucSequent("[x:=1;][{x:=x+1;}*]x>0".asFormula)
    val assignT = locateSucc(boxAssignEqualT)
    getProofSequent(assignT, new RootNode(s)) should be (
      sucSequent("\\forall x_1 (x_1 = 1 -> [x_0:=x_1;][{x_0:=x_0+1;}*]x_0>0)".asFormula))
  }

  it should "work in front of an ODE" in {
    import HybridProgramTacticsImpl.boxAssignEqualT
    val s = sucSequent("[x:=1;][{x'=1}]x>0".asFormula)
    val assignT = locateSucc(boxAssignEqualT)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall x_1 (x_1=1 -> [x_0:=x_1;][{x_0'=1}]x_0>0)".asFormula)))
  }

  // TODO not yet supported (partial variable writing)
  ignore should "not rename assignment lhs in may-bound" in {
    val s = sucSequent("[x:=z;][y:=y_0;{y:=y+1; ++ x:=x-1;}]x<=y".asFormula)
    val assignT = locateSucc(boxAssignEqualT)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall x_0 (x_0=z -> [y:=y_0;{y:=y+1; ++ x:=x_0-1;}]x<=y)".asFormula)))
  }

  it should "not rename must-bound x" in {
    val s = sucSequent("[x:=z;][y:=y_0;{x:=x;y:=y+1; ++ x:=x-1;}]x<=y".asFormula)
    val assignT = locateSucc(boxAssignEqualT)
    helper.runTactic(assignT, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sucSequent("\\forall x_0 (x_0=z -> [y:=y_0;{x:=x_0;y:=y+1; ++ x:=x_0-1;}]x<=y)".asFormula)))
  }

  "Combined box assign tactics" should "handle assignment in front of an ODE" in {
    import TacticLibrary.boxAssignT
    val s = sucSequent("[x:=1;][{x'=1}]x>0".asFormula)
    val assignT = locateSucc(boxAssignT)
    val result = helper.runTactic(assignT, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x_2=1".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "[{x_2'=1}]x_2>0".asFormula
  }

  it should "handle arbitrary assignments to variables not mentioned in subsequent formulas" in {
    import HybridProgramTacticsImpl.boxAssignT
    val tactic = locateSucc(boxAssignT)
    val result = helper.runTactic(tactic, new RootNode(sucSequent("[y_0:=y;][{y'=2}]y>0".asFormula)))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "y_2=y".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "[{y'=2}]y>0".asFormula
  }

  it should "handle arbitrary assignments and not fail continuation" in {
    import HybridProgramTacticsImpl.boxAssignT
    val tactic = locateSucc(boxAssignT) & locateSucc(diffWeakenT)
    val result = helper.runTactic(tactic, new RootNode(sucSequent("[x_0:=x;][{x'=2}]x>0".asFormula)))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x_2=x".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "true -> x_3>0".asFormula
  }

  it should "handle assignment in front of a loop" in {
    import TacticLibrary.boxAssignT
    val s = sucSequent("[x:=1;][{x:=x+1;}*]x>0".asFormula)
    val assignT = locateSucc(boxAssignT)
    val result = helper.runTactic(assignT, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x_2=1".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "[{x_2:=x_2+1;}*]x_2>0".asFormula
  }

  it should "be applicable in the antecedent" in {
    import TacticLibrary.boxAssignT
    val s = sequent(Nil, "[x:=x+1;]x>0".asFormula :: Nil, Nil)
    val assignT = locateAnte(boxAssignT)
    getProofSequent(assignT, new RootNode(s)) should be (sequent(Nil, "\\forall x_0 (x_0=x+1 -> x_0>0)".asFormula :: Nil, Nil))
  }

  // TODO not yet implemented
  ignore should "use the appropriate axiom variant" in {
    import TacticLibrary.boxAssignT
    val s = sequent(Nil, "[x:=1;]x>0".asFormula :: Nil, Nil)
    getProofSequent(locateAnte(boxAssignT), new RootNode(s)) should be (sequent(Nil, "1>0".asFormula :: Nil, Nil))
    val t = sucSequent("[x:=1;]x>0".asFormula)
    getProofSequent(locateSucc(boxAssignT), new RootNode(t)) should be (sucSequent("1>0".asFormula))
    val u = sucSequent("[x:=x+1;]x>0".asFormula)
    val result = helper.runTactic(locateSucc(boxAssignT), new RootNode(u))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x_1=x+1".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "x_1>0".asFormula
  }

  it should "use the skolemization method asked for" in {
    import HybridProgramTacticsImpl.boxAssignT
    val s = sucSequent("[x:=1;]x>0".asFormula)
    val result1 = helper.runTactic(locateSucc(boxAssignT(FOQuantifierTacticsImpl.skolemizeT)), new RootNode(s))
    result1.openGoals() should have size 1
    result1.openGoals().flatMap(_.sequent.ante) should contain only "x_1=1".asFormula
    result1.openGoals().flatMap(_.sequent.succ) should contain only "x_1>0".asFormula
    val result2 = helper.runTactic(locateSucc(boxAssignT(FOQuantifierTacticsImpl.skolemizeToFnT)), new RootNode(s))
    result2.openGoals() should have size 1
    result2.openGoals().flatMap(_.sequent.ante) should contain only "x_1()=1".asFormula
    result2.openGoals().flatMap(_.sequent.succ) should contain only "x_1()>0".asFormula
  }

  "Substitution box assignment" should "work on self assignment" in {
    val assignT = locateSucc(HybridProgramTacticsImpl.substitutionBoxAssignT)
    getProofSequent(assignT, new RootNode(sucSequent("[y:=y;]y>0".asFormula))) should be (sucSequent("y>0".asFormula))
    getProofSequent(assignT, new RootNode(sucSequent("[y:=y;][y:=2;]y>0".asFormula))) should be (sucSequent("[y:=2;]y>0".asFormula))
//    getProofSequent(assignT, new RootNode(sucSequent("[y:=y;][{y:=y+1;}*;]y>0".asFormula))) should be (sucSequent("[{y:=y+1;}*;]y>0".asFormula))
  }

  it should "update self assignments" in {
    val assignT = locateSucc(HybridProgramTacticsImpl.substitutionBoxAssignT)
    getProofSequent(assignT, new RootNode(sucSequent("[y:=z;][y:=y;]y>0".asFormula))) should be (sucSequent("[y:=z;]y>0".asFormula))
  }

  ignore should "handle self assignments inside formulas" in {
    val tacticFactory = PrivateMethod[PositionTactic]('v2tBoxAssignT)
    val assignT = (HybridProgramTacticsImpl invokePrivate tacticFactory())(new SuccPosition(0, new PosInExpr(0 :: Nil)))
    // equivalence rewriting will not go past bound y in \\forall y
    getProofSequent(assignT, new RootNode(sucSequent("\\forall y [y:=y;]y>0".asFormula))) should be (
      sucSequent("\\forall y y>0".asFormula))
  }

  "Substitution diamond assignment" should "work on self assignment" in {
    val assignT = locateSucc(HybridProgramTacticsImpl.substitutionDiamondAssignT)
    getProofSequent(assignT, new RootNode(sucSequent("<y:=y;>y>0".asFormula))) should be (sucSequent("y>0".asFormula))
    getProofSequent(assignT, new RootNode(sucSequent("<y:=y;><y:=2;>y>0".asFormula))) should be (sucSequent("<y:=2;>y>0".asFormula))
  }

  it should "update self assignments" in {
    val assignT = locateSucc(HybridProgramTacticsImpl.substitutionDiamondAssignT)
    getProofSequent(assignT, new RootNode(sucSequent("<y:=z;><y:=y;>y>0".asFormula))) should be (sucSequent("<y:=z;>y>0".asFormula))
  }

  it should "assign terms in simple predicates" in {
    val assignT = locateSucc(HybridProgramTacticsImpl.substitutionDiamondAssignT)
    getProofSequent(assignT, new RootNode(sucSequent("<y:=z+5*y;>y>0".asFormula))) should be (sucSequent("z+5*y>0".asFormula))
  }

  "Box test tactic" should "use axiom [?H]p <-> (H->p)" in {
    import TacticLibrary.boxTestT
    val s = sucSequent("[?y>2;]y>0".asFormula)
    val tactic = locateSucc(boxTestT)
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("y>2 -> y>0".asFormula))
  }

  "Diamond test tactic" should "use axiom <?H>p <-> (H & p)" in {
    import HybridProgramTacticsImpl.diamondTestT
    val s = sucSequent("<?y>2;>y>0".asFormula)
    val tactic = locateSucc(diamondTestT)
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("y>2 & y>0".asFormula))
  }

  "Box nondeterministic assignment tactic" should "introduce universal quantifier and rename free variables" in {
    import TacticLibrary.boxNDetAssign
    val s = sequent(Nil, "y>0".asFormula :: Nil, "[y:=*;]y>0".asFormula :: Nil)
    val tactic = locateSucc(boxNDetAssign)
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "y>0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "\\forall y y>0".asFormula
  }

  it should "rename free variables in modality predicates" in {
    import TacticLibrary.boxNDetAssign
    val s = sequent(Nil, "y>0".asFormula :: Nil, "[y:=*;][z:=2;](y>0 & z>0)".asFormula :: Nil)
    val assignT = locateSucc(boxNDetAssign)
    val result = helper.runTactic(assignT, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "y>0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "\\forall y [z:=2;](y>0 & z>0)".asFormula
  }

  it should "rename free variables but not bound variables (subsequent skolemization will, however)" in {
    import TacticLibrary.boxNDetAssign
    val s = sequent(Nil, "y>0".asFormula :: Nil, "[y:=*;][y:=2;]y>0".asFormula :: Nil)
    val assignT = locateSucc(boxNDetAssign)
    val result = helper.runTactic(assignT, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "y>0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "\\forall y [y:=2;]y>0".asFormula
  }

  it should "rename free variables but not variables bound by assignment in modality predicates (subsequent skolemization will, however)" in {
    import TacticLibrary.boxNDetAssign
    val s = sequent(Nil, "y>0".asFormula :: Nil, "[y:=*;][y:=2+y;]y>0".asFormula :: Nil)
    val assignT = locateSucc(boxNDetAssign)
    val result = helper.runTactic(assignT, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "y>0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "\\forall y [y:=2+y;]y>0".asFormula
  }

  it should "rename free variables but not variables bound by ODEs in modality predicates" in {
    import TacticLibrary.boxNDetAssign
    val s = sequent(Nil, "y>0".asFormula :: Nil, "[y:=*;][{z'=2+y}](y>0 & z>0)".asFormula :: Nil)
    val assignT = locateSucc(boxNDetAssign)
    val result = helper.runTactic(assignT, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "y>0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "\\forall y [{z'=2+y}](y>0 & z>0)".asFormula
  }

  it should "work in front of any discrete program" in {
    // TODO test all, but probably not in one shot
    import TacticLibrary.{boxNDetAssign, skolemizeT, ImplyRightT}
    val s = sequent(Nil, "y>0".asFormula :: Nil, "[y:=*;][y:=*;][?y>1;]y>0".asFormula :: Nil)
    val assignT = locateSucc(boxNDetAssign) & debugT("ndet") & locateSucc(skolemizeT) & locateSucc(ImplyRightT)

    val afterFirst = helper.runTactic(assignT, new RootNode(s))
    afterFirst.openGoals() should have size 1
    afterFirst.openGoals().flatMap(_.sequent.ante) should contain only "y>0".asFormula
    afterFirst.openGoals().flatMap(_.sequent.succ) should contain only "[y_0:=*;][?y_0>1;]y_0>0".asFormula

    val afterSecond = helper.runTactic(assignT, afterFirst.openGoals()(0))
    afterSecond.openGoals() should have size 1
    afterSecond.openGoals().flatMap(_.sequent.ante) should contain only "y>0".asFormula
    afterSecond.openGoals().flatMap(_.sequent.succ) should contain only "[?y_0>1;]y_0>0".asFormula
  }

  it should "work in front of a loop" in {
    val s = sucSequent("[y:=*;][{y:=y+2;}*]y>0".asFormula)
    val assignT = locateSucc(boxNDetAssign)
    val result = helper.runTactic(assignT, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "\\forall y [{y:=y+2;}*]y>0".asFormula
  }

  it should "work in front of a continuous program" in {
    val s = sucSequent("[y:=*;][{y'=2}]y>0".asFormula)
    val assignT = locateSucc(boxNDetAssign)
    val result = helper.runTactic(assignT, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "\\forall y [{y'=2}]y>0".asFormula
  }

  it should "work in front of a continuous program, even if it is not top-level" in {
    val s = sucSequent("[y:=*;][z:=2;][t:=0; {y'=2*y}]y>0".asFormula)
    val assignT = locateSucc(boxNDetAssign)
    val result = helper.runTactic(assignT, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "\\forall y [z:=2;][t:=0; {y'=2*y}]y>0".asFormula
  }

  "Diamond nondeterministic assignment tactic" should "introduce existential quantifier and rename free variables" in {
    val s = sequent(Nil, "y>0".asFormula :: Nil, "<y:=*;>y>0".asFormula :: Nil)
    val tactic = locateSucc(diamondNDetAssign)
    getProofSequent(tactic, new RootNode(s)) should be (
      sequent(Nil, "y>0".asFormula :: Nil, "\\exists y y>0".asFormula :: Nil))
  }

  it should "work with subsequent box modality" in {
    val s = sequent(Nil, "y>0".asFormula :: Nil, "<y:=*;>[z:=2;](y>0 & z>0)".asFormula :: Nil)
    val assignT = locateSucc(diamondNDetAssign)
    getProofSequent(assignT, new RootNode(s)) should be (
      sequent(Nil, "y>0".asFormula :: Nil, "\\exists y [z:=2;](y>0 & z>0)".asFormula :: Nil))
  }

  it should "work with subsequent assignment to same variable" in {
    val s = sucSequent("<y:=*;><y:=2;>y>0".asFormula)
    val assignT = locateSucc(diamondNDetAssign)
    getProofSequent(assignT, new RootNode(s)) shouldBe sucSequent("\\exists y <y:=2;>y>0".asFormula)
  }

  it should "work with possible subsequent assignment to same variable" in {
    val s = sucSequent("< y:=*;><y:=2;++z:=1;>(y>0 | z>0)".asFormula)
    val assignT = locateSucc(diamondNDetAssign)
    getProofSequent(assignT, new RootNode(s)) shouldBe sucSequent("\\exists y <y:=2;++z:=1;>(y>0 | z>0)".asFormula)
  }

  it should "neither rename free variables nor variables bound by assignment in modality predicates" in {
    val s = sequent(Nil, "y>0".asFormula :: Nil, "<y:=*;>[y:=2+y;]y>0".asFormula :: Nil)
    val assignT = locateSucc(diamondNDetAssign)
    getProofSequent(assignT, new RootNode(s)) should be (
      sequent(Nil, "y>0".asFormula :: Nil, "\\exists y [y:=2+y;]y>0".asFormula :: Nil))
  }

  it should "rename free variables but not variables bound by ODEs in modality predicates" in {
    val s = sequent(Nil, "y>0".asFormula :: Nil, "<y:=*;>[{z'=2+y}](y>0 & z>0)".asFormula :: Nil)
    val assignT = locateSucc(diamondNDetAssign)
    getProofSequent(assignT, new RootNode(s)) should be (
      sequent(Nil, "y>0".asFormula :: Nil, "\\exists y [{z'=2+y}](y>0 & z>0)".asFormula :: Nil))
  }

  it should "work in front of a loop" in {
    val s = sequent(Nil, "y>0".asFormula :: Nil, "<y:=*;><{y:=y+2;}*>y>0".asFormula :: Nil)
    val assignT = locateSucc(diamondNDetAssign)
    val assignResult = helper.runTactic(assignT, new RootNode(s))
    assignResult.openGoals() should have size 1
    assignResult.openGoals().flatMap(_.sequent.ante) should contain only "y>0".asFormula
    assignResult.openGoals().flatMap(_.sequent.succ) should contain only "\\exists y <{y:=y+2;}*>y>0".asFormula

    // TODO not yet supported
//    val tactic =
//      locateSucc(FOQuantifierTacticsImpl.instantiateT(Variable("y", None, Real), "z".asTerm)) /*&
//      locateSucc(v2vAssignT)*/
//    val result = helper.runTactic(tactic, assignResult.openGoals().head)
//    result.openGoals() should have size 1
//    result.openGoals().flatMap(_.sequent.ante) should contain only "y>0".asFormula
//    result.openGoals().flatMap(_.sequent.succ) should contain only "<{z:=z+2;}*;>z>0".asFormula
  }

  it should "work in front of a continuous program" in {
    val s = sucSequent("<y:=*;><{y'=2}>y>0".asFormula)
    val assignT = locateSucc(diamondNDetAssign)
    getProofSequent(assignT, new RootNode(s)) should be (
      sequent(Nil, Nil, "\\exists y <{y'=2}>y>0".asFormula :: Nil))
  }

  "Substitution box assignment" should "replace with variables" in {
    val s = sucSequent("[y:=z;]y>0".asFormula)
    val assignT = locateSucc(HybridProgramTacticsImpl.substitutionBoxAssignT)
    getProofSequent(assignT, new RootNode(s)) should be (
      sucSequent("z>0".asFormula))
  }

  it should "work with arbitrary terms" in {
    val s = sucSequent("[y:=1;][y:=y;]y>0".asFormula)
    val assignT = locateSucc(HybridProgramTacticsImpl.substitutionBoxAssignT)
    getProofSequent(assignT, new RootNode(s)) should be (sucSequent("[y:=1;]y>0".asFormula))
  }

  it should "not apply when immediately followed by an ODE or loop" in {
    val tactic = locateSucc(HybridProgramTacticsImpl.substitutionBoxAssignT)
    tactic.applicable(new RootNode(sucSequent("[y:=z;][{y'=z+1}]y>0".asFormula))) shouldBe false
    tactic.applicable(new RootNode(sucSequent("[y:=z;][{y:=z+1;}*]y>0".asFormula))) shouldBe false
  }

  "v2vAssignT" should "work on box ODEs" in {
    import HybridProgramTacticsImpl.v2vAssignT
    val tactic = locateSucc(v2vAssignT)
    getProofSequent(tactic, new RootNode(sucSequent("[y:=z;][{y'=2}]y>0".asFormula))) should be (sucSequent("[{z'=2}]z>0".asFormula))
  }

  it should "work in the antecedent" in {
    import HybridProgramTacticsImpl.v2vAssignT
    val tactic = locateAnte(v2vAssignT)
    getProofSequent(tactic, new RootNode(sequent(Nil, "[y:=z;][{y'=2}]y>0".asFormula :: Nil, Nil))) should be (
      sequent(Nil, "[{z'=2}]z>0".asFormula :: Nil, Nil))
  }


  it should "work on box loops" in {
    val s = sucSequent("[y:=z;][{y:=y+2;}*]y>0".asFormula)
    import HybridProgramTacticsImpl.v2vAssignT
    val tactic = locateSucc(v2vAssignT)
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("[{z:=z+2;}*]z>0".asFormula))
  }

  // TODO stuttering now creates boxes
  ignore should "work on diamond ODEs" in {
    import HybridProgramTacticsImpl.v2vAssignT
    val tactic = locateSucc(v2vAssignT)
    getProofSequent(tactic, new RootNode(sucSequent("<y:=z;><{y'=2}>y>0".asFormula))) should be (
      sucSequent("<{z'=2}>z>0".asFormula))
  }

  // TODO stuttering now creates boxes
  ignore should "work on diamond ODEs inside formulas" in {
    import HybridProgramTacticsImpl.v2vAssignT
    val tactic = v2vAssignT(SuccPosition(0, PosInExpr(1::Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("x>y & <y:=z;><{y'=2}>y>0".asFormula))) should be (
      sucSequent("x>y & <{z'=2}>z>0".asFormula))
  }

  // TODO stuttering now creates boxes
  ignore should "work on diamond loops" in {
    val s = sucSequent("<y:=z;><{y:=y+2;}*>y>0".asFormula)
    import HybridProgramTacticsImpl.v2vAssignT
    val tactic = locateSucc(v2vAssignT)
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("<{z:=z+2;}*>z>0".asFormula))
  }

  it should "work inside formulas" in {
    import HybridProgramTacticsImpl.v2vAssignT
    val tactic = v2vAssignT(SuccPosition(0, PosInExpr(1::0::Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("x=y & ([y:=z;][{y'=2}]y>0 | y>0)".asFormula))) should be (
      sucSequent("x=y & ([{z'=2}]z>0 | y>0)".asFormula))
  }

  "Discrete ghost" should "introduce assignment to fresh variable" in {
    val tactic = locateSucc(discreteGhostT(None, new Variable("y", None, Real)))
    getProofSequent(tactic, new RootNode(sucSequent("y>0".asFormula))) should be (
      sucSequent("[y_0:=y;]y_0>0".asFormula))
  }

  it should "assign term t to fresh variable" in {
    val tactic = locateSucc(discreteGhostT(Some(new Variable("z", None, Real)),
      "y+1".asTerm))
    getProofSequent(tactic, new RootNode(sucSequent("y+1>0".asFormula))) should be (
      sucSequent("[z:=y+1;]z>0".asFormula))
  }

  it should "allow arbitrary terms t when a ghost name is specified" in {
    val tactic = locateSucc(discreteGhostT(Some(Variable("z", None, Real)), "x+5".asTerm))
    getProofSequent(tactic, new RootNode(sucSequent("y>0".asFormula))) should be (
      sucSequent("[z:=x+5;]y>0".asFormula))
  }

  it should "not allow arbitrary terms t when no ghost name is specified" in {
    val tactic = locateSucc(discreteGhostT(None, "x+5".asTerm))
    an [IllegalArgumentException] should be thrownBy helper.runTactic(tactic, new RootNode(sucSequent("y>0".asFormula)))
  }

  it should "use same variable if asked to do so" in {
    val tactic = locateSucc(discreteGhostT(Some(new Variable("y", None, Real)), new Variable("y", None, Real)))
    getProofSequent(tactic, new RootNode(sucSequent("y>0".asFormula))) should be (
      sucSequent("[y:=y;]y>0".asFormula))
  }

  it should "use specified fresh variable" in {
    val tactic = locateSucc(discreteGhostT(Some(new Variable("z", None, Real)), new Variable("y", None, Real)))
    getProofSequent(tactic, new RootNode(sucSequent("y>0".asFormula))) should be (
      sucSequent("[z:=y;]z>0".asFormula))
  }

  it should "not accept variables present in f" in {
    val tactic = locateSucc(discreteGhostT(Some(new Variable("z", None, Real)), new Variable("y", None, Real)))
    an [IllegalArgumentException] should be thrownBy helper.runTactic(tactic, new RootNode(sucSequent("y>z+1".asFormula)))
  }

  it should "work on assignments" in {
    val tactic = locateSucc(discreteGhostT(None, Variable("y", None, Real)))
    getProofSequent(tactic, new RootNode(sucSequent("[y:=2;]y>0".asFormula))) should be (
      sucSequent("[y_0:=y;][y:=2;]y>0".asFormula))
  }

  it should "introduce ghosts in the middle of formulas" in {
    val tactic = discreteGhostT(None, Variable("y", None, Real))(new SuccPosition(0, new PosInExpr(1 :: Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("[x:=1;][y:=2;]y>0".asFormula))) should be (
      sucSequent("[x:=1;][y_0:=y;][y:=2;]y>0".asFormula))
  }

  it should "introduce self-assignment ghosts in the middle of formulas when not bound before" in {
    val tactic = discreteGhostT(Some(Variable("y", None, Real)), Variable("y", None, Real))(new SuccPosition(0, new PosInExpr(1 :: Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("[x:=1;][y:=2;]y>0".asFormula))) should be (
      sucSequent("[x:=1;][y:=y;][y:=2;]y>0".asFormula))
  }

  it should "not introduce self-assignment ghosts in the middle of formulas when bound" in {
    val tactic = discreteGhostT(Some(Variable("x", None, Real)), Variable("x", None, Real))(new SuccPosition(0, new PosInExpr(1 :: Nil)))
    // TODO for some reason the exception is thrown but still not satisfies the test
    /*a [SubstitutionClashException] should be thrownBy*/ helper.runTactic(tactic, new RootNode(sucSequent("[x:=x+1;][{x'=2}]x>0".asFormula)))
  }

  ignore should "introduce ghosts in modality predicates" in {
    // will not work because y is bound by y:=2, so equality rewriting does not work
    val tactic = discreteGhostT(None, Variable("y", None, Real))(new SuccPosition(0, new PosInExpr(1 :: Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("[y:=2;]y>0".asFormula))) should be (
      sucSequent("[y:=2;][y_0:=y;]y>0".asFormula))
  }

  it should "work on loops" in {
    val tactic = locateSucc(discreteGhostT(None, Variable("y", None, Real)))
    getProofSequent(tactic, new RootNode(sucSequent("[{y:=y+1;}*]y>0".asFormula))) should be (
      sucSequent("[y_0:=y;][{y:=y+1;}*]y>0".asFormula))
  }

  it should "work on ODEs" in {
    val tactic = locateSucc(discreteGhostT(None, Variable("y", None, Real)))
    getProofSequent(tactic, new RootNode(sucSequent("[{y'=1}]y>0".asFormula))) should be (
      sucSequent("[y_0:=y;][{y'=1}]y>0".asFormula))
  }

  it should "not propagate arbitrary terms into ODEs" in {
    val tactic = locateSucc(discreteGhostT(Some(Variable("z", None, Real)),
      "y+1".asTerm))
    // would like to check for exception, but not possible because of Scheduler
    getProofSequent(tactic, new RootNode(sucSequent("[{y'=1}]y>0".asFormula))) should be (
      sucSequent("[z:=y+1;][{y'=1}]y>0".asFormula))
  }

  it should "abbreviate terms in a formula" in {
    val tactic = locateSucc(discreteGhostT(Some(Variable("z", None, Real)),
      "0".asTerm))
    getProofSequent(tactic, new RootNode(sucSequent("[x:=5+0;]x>0".asFormula))) should be (
      sucSequent("[z:=0;][x:=5+z;]x>z".asFormula))
  }

  "nonAbbrDiscreteGhost" should "not abbreviate terms in a formula" in {
    import HybridProgramTacticsImpl.nonAbbrvDiscreteGhostT
    val tactic = locateSucc(nonAbbrvDiscreteGhostT(Some(Variable("z", None, Real)), "0".asTerm))
    getProofSequent(tactic, new RootNode(sucSequent("[x:=5+0;]x>0".asFormula))) should be (
      sucSequent("[z:=0;][x:=5+0;]x>0".asFormula))
  }

  "Induction tactic" should "rename all bound variables" in {
    val tactic = locateSucc(inductionT(Some("x*y>5".asFormula)))
    val result = getProofSequent(tactic, new RootNode(
      sequent(Nil,
        "x>0".asFormula :: "y>1".asFormula :: Nil,
        "[{x:=2;}*]x>2".asFormula :: "x<3".asFormula :: "y<4".asFormula :: Nil)))

    result shouldBe a [List[Sequent]]
    result.asInstanceOf[List[Sequent]] should contain only (
      sequent(Nil,
        "x>0".asFormula :: "y>1".asFormula :: Nil,
        "x<3".asFormula :: "y<4".asFormula :: "\\forall x (x*y>5 -> [x:=2;]x*y>5)".asFormula :: Nil
      ),
      sequent(Nil,
        "x>0".asFormula :: "y>1".asFormula :: Nil,
        "x<3".asFormula :: "y<4".asFormula :: "\\forall x (x*y>5 -> x>2)".asFormula :: Nil
      ),
      sequent(Nil,
        "x>0".asFormula :: "y>1".asFormula :: Nil,
        "x<3".asFormula :: "y<4".asFormula :: "x*y>5".asFormula :: Nil
      )
    )
  }

  "Wipe context induction tactic" should "wipe all formulas mentioning bound variables from the context" in {
    import HybridProgramTacticsImpl.wipeContextInductionT
    val tactic = locateSucc(wipeContextInductionT(Some("x*y>5".asFormula)))

    val result = helper.runTactic(tactic, new RootNode(
      sequent(Nil,
        "x>0".asFormula :: "y>1".asFormula :: "z>7".asFormula :: Nil,
        "[{x:=2;}*]x>2".asFormula :: "x<3".asFormula :: "y<4".asFormula :: Nil)))

    result.openGoals() should have size 3
    result.openGoals()(0).sequent.ante should contain only ("x>0".asFormula, "y>1".asFormula, "z>7".asFormula)
    result.openGoals()(0).sequent.succ should contain only ("x<3".asFormula, "y<4".asFormula, "x*y>5".asFormula)
    result.openGoals()(1).sequent.ante should contain only ("y>1".asFormula, "z>7".asFormula)
    result.openGoals()(1).sequent.succ should contain only ("y<4".asFormula, "x*y>5 -> x>2".asFormula)
    result.openGoals()(2).sequent.ante should contain only ("y>1".asFormula, "z>7".asFormula)
    result.openGoals()(2).sequent.succ should contain only ("y<4".asFormula, "x*y>5 -> [x:=2;]x*y>5".asFormula)
  }

  // TODO loops where MBV != BV not yet supported
  ignore should "do the same with a slightly more complicated formula" in {
    import HybridProgramTacticsImpl.wipeContextInductionT
    val tactic = locateSucc(wipeContextInductionT(Some("x*y>5".asFormula)))

    val result = helper.runTactic(tactic, new RootNode(
      sequent(Nil,
        "x>0".asFormula :: "y>1".asFormula :: "z>7".asFormula :: Nil,
        "[{x:=2 ++ y:=z;}*]x>2".asFormula :: "x<3".asFormula :: "y<4".asFormula :: Nil)))

    result.openGoals() should have size 3
    result.openGoals()(0).sequent.ante should contain only ("x>0".asFormula, "y>1".asFormula, "z>7".asFormula)
    result.openGoals()(0).sequent.succ should contain only ("x<3".asFormula, "y<4".asFormula, "x*y>5".asFormula)
    result.openGoals()(1).sequent.ante should contain only "z>7".asFormula
    result.openGoals()(1).sequent.succ should contain only "x*y>5 -> x>2".asFormula
    result.openGoals()(2).sequent.ante should contain only "z>7".asFormula
    result.openGoals()(2).sequent.succ should contain only "x*y>5 -> [x:=2 ++ y:=z;]x*y>5".asFormula
  }

  it should "remove duplicated formulas" in {
    import HybridProgramTacticsImpl.wipeContextInductionT
    val tactic = locateSucc(wipeContextInductionT(Some("x*y>5".asFormula)))

    val result = helper.runTactic(tactic, new RootNode(
      sequent(Nil,
        "x>0".asFormula :: "x>0".asFormula :: "y>1".asFormula :: "z>7".asFormula :: Nil,
        "[{x:=2;}*]x>2".asFormula :: "x<3".asFormula :: "x<3".asFormula :: "y<4".asFormula :: Nil)))

    result.openGoals() should have size 3
    result.openGoals()(0).sequent.ante should contain only ("x>0".asFormula, "y>1".asFormula, "z>7".asFormula)
    result.openGoals()(0).sequent.succ should contain only ("x<3".asFormula, "y<4".asFormula, "x*y>5".asFormula)
    result.openGoals()(1).sequent.ante should contain only ("y>1".asFormula, "z>7".asFormula)
    result.openGoals()(1).sequent.succ should contain only ("y<4".asFormula, "x*y>5 -> x>2".asFormula)
    result.openGoals()(2).sequent.ante should contain only ("y>1".asFormula, "z>7".asFormula)
    result.openGoals()(2).sequent.succ should contain only ("y<4".asFormula, "x*y>5 -> [x:=2;]x*y>5".asFormula)
  }

  "Derivative assignment" should "introduce universal quantifier and rename appropriately" in {
    val tactic = locateSucc(boxDerivativeAssignT)
    getProofSequent(tactic, new RootNode(sucSequent("[x':=y;]x'>0".asFormula))) should be (
      sucSequent("y>0".asFormula)
    )
  }

  it should "not rename when there is nothing to rename" in {
    val tactic = locateSucc(boxDerivativeAssignT)
    getProofSequent(tactic, new RootNode(sucSequent("[x':=y;]y>0".asFormula))) should be (
      sucSequent("y>0".asFormula)
    )
  }

  it should "work with subsequent ODEs" in {
    val tactic = boxDerivativeAssignT(SuccPosition(0))
    getProofSequent(tactic, new RootNode(sucSequent("[x':=y;][{y'=z}]y>0".asFormula))) should be (
      sucSequent("[{y'=z}]y>0".asFormula)
    )
  }

  it should "rename free occurrences in subsequent modalities" in {
    val tactic = boxDerivativeAssignT(SuccPosition(0, PosInExpr(1::Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("[x':=y;][y':=z;]x'+y'>0".asFormula))) should be (
      sucSequent("[x':=y;]x'+z>0".asFormula)
    )
  }

  it should "work on mutual assignments" in {
    val tactic = boxDerivativeAssignT(SuccPosition(0, PosInExpr(1::Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("[x':=y;][y':=x;]x'+y'>0".asFormula))) should be (
      sucSequent("[x':=y;]x'+x>0".asFormula)
    )
  }

  it should "work inside out" in {
    val tactic = boxDerivativeAssignT(SuccPosition(0, PosInExpr(1::Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("[x':=y;][y':=x;]x'+y'>0".asFormula))) should be (
      sucSequent("[x':=y;]x'+x>0".asFormula)
    )
  }

  it should "work inside out when applied repeatedly" in {
    val tactic = locateSucc(boxDerivativeAssignT)
    getProofSequent(tactic*, new RootNode(sucSequent("[x':=y;][y':=x;]x'+y'>0".asFormula))) should be (
      sucSequent("y+x>0".asFormula)
    )
  }

  it should "work on non-trivial derivatives" in {
    val tactic = locateSucc(boxDerivativeAssignT)
    getProofSequent(tactic*, new RootNode(sucSequent("[x':=x;]2*x*x'>0".asFormula))) should be (
      sucSequent("2*x*x>0".asFormula)
    )
  }

  "Box choice" should "transform choice into a conjunction" in {
    val tactic = locateSucc(boxChoiceT)
    getProofSequent(tactic, new RootNode(sucSequent("[x:=2; ++ x:=3;]x>0".asFormula))) should be (
      sucSequent("[x:=2;]x>0 & [x:=3;]x>0".asFormula))
  }

  "Diamond choice" should "transform choice into a disjunction" in {
    val tactic = locateSucc(diamondChoiceT)
    getProofSequent(tactic, new RootNode(sucSequent("<x:=2; ++ x:=3;>x>0".asFormula))) should be (
      sucSequent("<x:=2;>x>0 | <x:=3;>x>0".asFormula))
  }

  "Box sequence" should "transform sequence into two boxes" in {
    import TacticLibrary.boxSeqT
    val tactic = locateSucc(boxSeqT)
    getProofSequent(tactic, new RootNode(sucSequent("[x:=2; x:=3;]x>0".asFormula))) should be (
      sucSequent("[x:=2;][x:=3;]x>0".asFormula))
  }

  "Diamond sequence" should "transform sequence into two diamonds" in {
    import HybridProgramTacticsImpl.diamondSeqT
    val tactic = locateSucc(diamondSeqT)
    getProofSequent(tactic, new RootNode(sucSequent("<x:=2; x:=3;>x>0".asFormula))) should be (
      sucSequent("<x:=2;><x:=3;>x>0".asFormula))
  }

  "Diamond duality" should "transform diamond into negated box" in {
    val tactic = locateSucc(HybridProgramTacticsImpl.diamondDualityT)
    getProofSequent(tactic, new RootNode(sucSequent("<x:=2; x:=3;>x>0".asFormula))) should be (
      sucSequent("![x:=2; x:=3;](!x>0)".asFormula))
  }

  it should "transform diamond into negated box inside a formula" in {
    val tactic = HybridProgramTacticsImpl.diamondDualityT(SuccPosition(0, PosInExpr(1::Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("v=5 & <x:=2; x:=3;>x>0".asFormula))) should be (
      sucSequent("v=5 & ![x:=2; x:=3;](!x>0)".asFormula))
  }

  it should "transform negated box into diamond" in {
    val tactic = locateSucc(HybridProgramTacticsImpl.diamondDualityT)
    getProofSequent(tactic, new RootNode(sucSequent("![x:=2; x:=3;](!x>0)".asFormula))) should be (
      sucSequent("<x:=2; x:=3;>x>0".asFormula))
  }

  "Box duality" should "transform box into negated diamond" in {
    val tactic = locateSucc(HybridProgramTacticsImpl.boxDualityT)
    getProofSequent(tactic, new RootNode(sucSequent("[x:=2; x:=3;]x>0".asFormula))) should be (
      sucSequent("!<x:=2; x:=3;>(!x>0)".asFormula))
  }

  it should "transform box into negated diamond inside a formula" in {
    val tactic = HybridProgramTacticsImpl.boxDualityT(SuccPosition(0, PosInExpr(1::Nil)))
    getProofSequent(tactic, new RootNode(sucSequent("v=5 & [x:=2; x:=3;]x>0".asFormula))) should be (
      sucSequent("v=5 & !<x:=2; x:=3;>(!x>0)".asFormula))
  }

  it should "transform negated diamond into box" in {
    val tactic = locateSucc(HybridProgramTacticsImpl.boxDualityT)
    getProofSequent(tactic, new RootNode(sucSequent("!<x:=2; x:=3;>(!x>0)".asFormula))) should be (
      sucSequent("[x:=2; x:=3;]x>0".asFormula))
  }

  "Box sequence generalization" should "split a box" in {
    val tactic = HybridProgramTacticsImpl.boxSeqGenT("true".asFormula)(SuccPosition(0))
    val s = sequent(Nil, "x=0".asFormula::Nil, "([x:=-1; x:=x+1;]x=1)".asFormula::Nil)
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 2
    result.openGoals().head.sequent.ante should contain only "true".asFormula
    result.openGoals().head.sequent.succ should contain only "[x:=x+1;]x=1".asFormula
    result.openGoals()(1).sequent.ante should contain only "x=0".asFormula
    result.openGoals()(1).sequent.succ should contain only "[x:=-1;]true".asFormula
  }

  it should "split a box when there is context around" in {
    val tactic = HybridProgramTacticsImpl.boxSeqGenT("true".asFormula)(SuccPosition(1))
    val s = sequent(Nil, "x=0".asFormula::"z=1".asFormula::Nil, "a=b".asFormula::"([x:=-1; x:=x+1;]x=1)".asFormula::"c=d".asFormula::Nil)
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 2
    result.openGoals().head.sequent.ante should contain only "true".asFormula
    result.openGoals().head.sequent.succ should contain only "[x:=x+1;]x=1".asFormula
    result.openGoals()(1).sequent.ante should contain only ("x=0".asFormula, "z=1".asFormula)
    result.openGoals()(1).sequent.succ should contain only ("[x:=-1;]true".asFormula, "a=b".asFormula, "c=d".asFormula)
  }

  "V vacuous" should "remove box on a simple predicate" in {
    val tactic = locateSucc(HybridProgramTacticsImpl.boxVacuousT)
    val s = sucSequent("[x:=2;]y>0".asFormula)
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "y>0".asFormula
  }

  it should "work in context" in {
    val tactic = HybridProgramTacticsImpl.boxVacuousT(SuccPosition(0, PosInExpr(1::Nil)))
    val s = sucSequent("[z:=3;][x:=2;]y>0".asFormula)
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[z:=3;]y>0".asFormula
  }

  it should "remove box on a universally quantified predicate" in {
    val tactic = locateSucc(HybridProgramTacticsImpl.boxVacuousT)
    val s = sucSequent("[x:=2;](\\forall x x>0)".asFormula)
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "\\forall x x>0".asFormula
  }
}
