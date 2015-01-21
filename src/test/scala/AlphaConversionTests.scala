import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.{AlphaConversionHelper, Tactics}
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{ApplyRule, Tactic, PositionTactic}
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import testHelper.StringConverter
import testHelper.SequentFactory._
import StringConverter._
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}

/**
* Created by smitsch on 1/13/15.
* @author Stefan Mitsch
* @author Ran Ji
*/
class AlphaConversionTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  val helper = new ProvabilityTestHelper((x) => println(x),
    new ToolBase("") { override def init(cfg: Map[String, String]) {} })

  def alpha(from: String, to: String): PositionTactic =
    new PositionTactic("Alpha Renaming") {
      override def applies(s: Sequent, p: Position): Boolean = true
      override def apply(p: Position): Tactic = new ApplyRule(new AlphaConversion(p, from, None, to, None)) {
        override def applicable(node: ProofNode): Boolean = true
      } & hideT(p.topLevel)
    }

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler.init(Map())
  }

  override def afterEach() = {
    Tactics.KeYmaeraScheduler.shutdown()
  }

  /**
   * ==================================================
   * test cases for \alpha-conversion rule
   */

  // (1) Forall(v, phi)

  "Apply alpha-conversion (x,t) on \\forall x. x>0" should "be \\forall t. t>0" in {
    val s = sequent(Nil, Nil, "\\forall x. x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "\\forall t. t>0".asFormula :: Nil)
    ))
  }

  // shouldn't it be \forall t. [t:=x+1;]t>0?
  "Apply alpha-conversion (x,t) on \\forall x. [x:=x+1;]x>0" should "be \\forall t. [t:=t+1;]t>0" in {
    val s = sequent(Nil, Nil, "\\forall x. [x:=x+1;]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "\\forall t. [t:=t+1;]t>0".asFormula :: Nil)
    ))
  }

  "Apply alpha-conversion (x,t) on \\forall x. [y:=x+1;]x>0" should "be \\forall t. [y:=t+1;]t>0" in {
    val s = sequent(Nil, Nil, "\\forall x. [y:=x+1;]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "\\forall t. [y:=t+1;]t>0".asFormula :: Nil)
    ))
  }

  "Apply alpha-conversion (x,t) on \\forall x. [x:=x+1;][y:=x+1;]x>0" should "be \\forall t. [t:=t+1;][y:=t+1;]t>0" in {
    val s = sequent(Nil, Nil, "\\forall x. [x:=x+1;][y:=x+1;]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "\\forall t. [t:=t+1;][y:=t+1;]t>0".asFormula :: Nil)
    ))
  }

  // (2) Exists(v, phi)

  "Apply alpha-conversion (x,t) on \\exists x. x>0" should "be \\exists t. t>0" in {
    val s = sequent(Nil, Nil, "\\exists x. x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "\\exists t. t>0".asFormula :: Nil)
    ))
  }

  "Apply alpha-conversion (x,t) on \\exists x. [x:=x+1;]x>0" should "be \\exists t. [t:=t+1;]t>0" in {
    val s = sequent(Nil, Nil, "\\exists x. [x:=x+1;]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "\\exists t. [t:=t+1;]t>0".asFormula :: Nil)
    ))
  }

  "Apply alpha-conversion (x,t) on \\exists x. [x:=x+1;][y:=x+1;]x>0" should "be \\exists t. [t:=t+1;][y:=t+1;]t>0" in {
    val s = sequent(Nil, Nil, "\\exists x. [x:=x+1;][y:=x+1;]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "\\exists t. [t:=t+1;][y:=t+1;]t>0".asFormula :: Nil)
    ))
  }

  // (3) Modality(BoxModality(Assign(x, e)), phi)

  "Apply alpha-conversion (x,t) on [x:=x+1;]x>0" should "be [t:=x+1;]t>0" in {
    val s = sequent(Nil, Nil, "[x:=x+1;]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "[t:=x+1;]t>0".asFormula :: Nil)
    ))
  }

  // should work with new alpha conversion rule
  "Apply alpha-conversion (x,t) on [y:=x+1;]x>0"
  ignore should "be [y:=x+1;]x>0" in {
    val s = sequent(Nil, Nil, "[y:=x+1;]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "[y:=x+1;]x>0".asFormula :: Nil)
    ))
  }

  // should work with new alpha conversion rule
  "Apply alpha-conversion (x,t) on [x:=x+1;][y:=x+1;]x>0"
  ignore should "be [t:=x+1;][y:=x+1;]x>0" in {
    val s = sequent(Nil, Nil, "[x:=x+1;][y:=x+1;]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "[t:=x+1;][y:=t+1;]t>0".asFormula :: Nil)
    ))
  }

  "Apply alpha-conversion (x,t) on [x:=x+1;][x:=x+1;]x>0" should "be [t:=x+1;][x:=x+1;]x>0" in {
    val s = sequent(Nil, Nil, "[x:=x+1;][x:=x+1;]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "[t:=x+1;][t:=t+1;]t>0".asFormula :: Nil)
    ))
  }

  // (4) Modality(DiamondModality(Assign(x, e)), phi)

  "Apply alpha-conversion (x,t) on <x:=x+1;>x>0" should "be <t:=x+1;>t>0" in {
    val s = sequent(Nil, Nil, "<x:=x+1;>x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "<t:=x+1;>t>0".asFormula :: Nil)
    ))
  }

  // should work with new alpha conversion rule
  "Apply alpha-conversion (x,t) on <y:=x+1;>x>0"
  ignore should "be <y:=x+1;>x>0" in {
    val s = sequent(Nil, Nil, "<y:=x+1;>x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "<y:=x+1;>x>0".asFormula :: Nil)
    ))
  }

  // should work with new alpha conversion rule
  // "Apply alpha-conversion (x,t) on <x:=x+1;><y:=x+1;>x>0"
  ignore should "be <t:=x+1;><y:=x+1;>x>0" in {
    val s = sequent(Nil, Nil, "<x:=x+1;><y:=x+1;>x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "<t:=x+1;><y:=t+1;>t>0".asFormula :: Nil)
    ))
  }

  "Apply alpha-conversion (x,t) on <x:=x+1;><x:=x+1;>x>0" should "be <t:=x+1;><x:=x+1;>x>0" in {
    val s = sequent(Nil, Nil, "<x:=x+1;><x:=x+1;>x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "<t:=x+1;><t:=t+1;>t>0".asFormula :: Nil)
    ))
  }

  // (5) Modality(BoxModality(NDetAssign(x)), phi)

  // should work with new alpha conversion rule
  "Apply alpha-conversion (x,t) on [x:=1 ++ x:=x+1;]x>0"
  ignore should "be [t:=1 ++ t:=x+1;]t>0" in {
    val s = sequent(Nil, Nil, "[x:=1 ++ x:=x+1;]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "[t:=1 ++ t:=x+1;]t>0".asFormula :: Nil)
    ))
  }

  // should work with new alpha conversion rule
  "Apply alpha-conversion (x,t) on [{x:=1 ++ x:=x+1};{x:=1 ++ x:=x+1};]x>0"
  ignore should "be [{t:=1 ++ t:=x+1};{t:=1 ++ t:=t+1};]t>0" in {
    val s = sequent(Nil, Nil, "[{x:=1 ++ x:=x+1};{x:=1 ++ x:=x+1};]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "[{t:=1 ++ t:=x+1};{t:=1 ++ t:=t+1};]t>0".asFormula :: Nil)
    ))
  }

  // should work with new alpha conversion rule
  "Apply alpha-conversion (x,t) on [{x:=1 ++ x:=x+1}*;]x>0"
  ignore should "be [{t:=1 ++ t:=t+1}*;]t>0" in {
    val s = sequent(Nil, Nil, "[{x:=1 ++ x:=x+1}*;]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "[t:=x;][{t:=1 ++ t:=t+1}*;]t>0".asFormula :: Nil)
    ))
  }

  // should work with new alpha conversion rule
  "Apply alpha-conversion (x,t) on [x:=1 ++ x:=x+1 ++ z:=x;]x>0"
  ignore should "be [t:=1 ++ t:=x+1 ++ z:=x;]t>0" in {
    val s = sequent(Nil, Nil, "[x:=1 ++ x:=x+1 ++ z:=x;]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "[t:=1 ++ t:=x+1 ++ z:=x;]t>0".asFormula :: Nil)
    ))
  }

  // (6) Modality(DiamondModality(NDetAssign(x)), phi)

  // should work with new alpha conversion rule
  "Apply alpha-conversion (x,t) on <x:=1 ++ x:=x+1;>x>0"
  ignore should "be <t:=1 ++ t:=x+1;>t>0" in {
    val s = sequent(Nil, Nil, "<x:=1 ++ x:=x+1;>x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "<t:=1 ++ t:=x+1;>t>0".asFormula :: Nil)
    ))
  }

  // should work with new alpha conversion rule
  "Apply alpha-conversion (x,t) on <{x:=1 ++ x:=x+1};{x:=1 ++ x:=x+1};>x>0"
  ignore should "be <{t:=1 ++ t:=x+1};{t:=1 ++ t:=t+1};>t>0" in {
    val s = sequent(Nil, Nil, "<{x:=1 ++ x:=x+1};{x:=1 ++ x:=x+1};>x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "<{t:=1 ++ t:=x+1};{t:=1 ++ t:=t+1};>t>0".asFormula :: Nil)
    ))
  }

  // should work with new alpha conversion rule
  "Apply alpha-conversion (x,t) on <{x:=1 ++ x:=x+1}*;>x>0"
  ignore should "be <{t:=1 ++ t:=t+1}*;>t>0" in {
    val s = sequent(Nil, Nil, "<{x:=1 ++ x:=x+1}*;>x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "<t:=x;><{t:=1 ++ t:=t+1}*;>t>0".asFormula :: Nil)
    ))
  }

  // should work with new alpha conversion rule
  "Apply alpha-conversion (x,t) on <x:=1 ++ x:=x+1 ++ z:=x;>x>0"
  ignore should "be <t:=1 ++ t:=x+1 ++ z:=x;>t>0" in {
    val s = sequent(Nil, Nil, "<x:=1 ++ x:=x+1 ++ z:=x;>x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "<t:=1 ++ t:=x+1 ++ z:=x;>t>0".asFormula :: Nil)
    ))
  }

  // (7) Modality(BoxModality(ContEvolveProgram | IncompleteSystem, _), phi)

  "Apply alpha-conversion (x,t) on [x'=1;]x>0" should "be [t:=x;][t'=1;]t>0" in {
    val s = sequent(Nil, Nil, "[x'=1;]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "[t:=x;][t'=1;]t>0".asFormula :: Nil)
    ))
  }

  "Apply alpha-conversion (x,t) on [x'=x+1;]x>0" should "be [t:=x;][t'=t+1;]t>0" in {
    val s = sequent(Nil, Nil, "[x'=x+1;]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "[t:=x;][t'=t+1;]t>0".asFormula :: Nil)
    ))
  }

  "Apply alpha-conversion (x,t) on [$$x'=x+1$$;]x>0" should "be [t:=x;][$$t'=t+1$$;]t>0" in {
    val s = sequent(Nil, Nil, "[$$x'=x+1$$;]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "[t:=x;][$$t'=t+1$$;]t>0".asFormula :: Nil)
    ))
  }

  "Apply alpha-conversion (x,t) on [$$x'=x+1, y'=x$$;]x>0" should "be [t:=x;][$$t'=t+1,y'=t$$;]t>0" in {
    val s = sequent(Nil, Nil, "[$$x'=x+1,y'=x$$;]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "[t:=x;][$$t'=t+1,y'=t$$;]t>0".asFormula :: Nil)
    ))
  }

  "Apply alpha-conversion (x,t) on [$$x'=x+1 & x>0, y'=x & y<x$$;]x>0" should "be [t:=x;][$$t'=t+1 & t>0,y'=t & y<t$$;]t>0" in {
    val s = sequent(Nil, Nil, "[$$x'=x+1 & x>0, y'=x & y<x$$;]x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "[t:=x;][$$t'=t+1 & t>0,y'=t & y<t$$;]t>0".asFormula :: Nil)
    ))
  }

  // (8) Modality(DiamondModality(ContEvolveProgram | IncompleteSystem, _), phi)

  "Apply alpha-conversion (x,t) on <x'=1;>x>0" should "be <t:=x;><t'=1;>t>0" in {
    val s = sequent(Nil, Nil, "<x'=1;>x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "<t:=x;><t'=1;>t>0".asFormula :: Nil)
    ))
  }

  "Apply alpha-conversion (x,t) on <x'=x+1;>x>0" should "be <t:=x;><t'=t+1;>t>0" in {
    val s = sequent(Nil, Nil, "<x'=x+1;>x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "<t:=x;><t'=t+1;>t>0".asFormula :: Nil)
    ))
  }

  "Apply alpha-conversion (x,t) on <$$x'=x+1$$;>x>0" should "be <t:=x;><$$t'=t+1$$;>t>0" in {
    val s = sequent(Nil, Nil, "<$$x'=x+1$$;>x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "<t:=x;><$$t'=t+1$$;>t>0".asFormula :: Nil)
    ))
  }

  "Apply alpha-conversion (x,t) on <$$x'=x+1, y'=x$$;>x>0" should "be <t:=x;><$$t'=t+1,y'=t$$;>t>0" in {
    val s = sequent(Nil, Nil, "<$$x'=x+1,y'=x$$;>x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "<t:=x;><$$t'=t+1,y'=t$$;>t>0".asFormula :: Nil)
    ))
  }

  "Apply alpha-conversion (x,t) on <$$x'=x+1 & x>0, y'=x & y<x$$;>x>0" should "be <t:=x;><$$t'=t+1 & t>0,y'=t & y<t$$;>t>0" in {
    val s = sequent(Nil, Nil, "<$$x'=x+1 & x>0, y'=x & y<x$$;>x>0".asFormula :: Nil)
    val tactic = locateSucc(alpha("x", "t"))
    helper.runTactic(tactic, new RootNode(s)).openGoals().foreach(_.sequent should be (
      sequent(Nil, Nil, "<t:=x;><$$t'=t+1 & t>0,y'=t & y<t$$;>t>0".asFormula :: Nil)
    ))
  }

  /**
   * ==================================================
   * test cases for AlphaConversionHelper
   */


  "AlphaConversionHelper" should "rename free variables" in {
    val x = new Variable("x", None, Real)
    AlphaConversionHelper.replaceFree("x>0".asFormula)(x, CDot) should be (
      GreaterThan(Real, CDot, Number(0)))
  }

  it should "rename free variables in modality predicates" in {
    val x = new Variable("x", None, Real)
    val z = new Variable("z", None, Real)
    AlphaConversionHelper.replaceFree("[z:=2;](x>0 & z>0)".asFormula)(x, CDot) should be (
      BoxModality(Assign(z, Number(2)), And(GreaterThan(Real, CDot, Number(0)), GreaterThan(Real, z, Number(0)))))
    }

  it should "not rename bound variables" in {
    val x = new Variable("x", None, Real)
    AlphaConversionHelper.replaceFree("[x:=2;]x>0".asFormula)(x, CDot) should be (
      BoxModality(Assign(x, Number(2)), GreaterThan(Real, x, Number(0))))
  }

  it should "be enforceable to not rename bound variables" in {
    val x = new Variable("x", None, Real)
    AlphaConversionHelper.replaceFree("[x:=2;]x>0".asFormula)(x, CDot, None) should be (
      BoxModality(Assign(CDot, Number(2)), GreaterThan(Real, CDot, Number(0))))
  }

  it should "rename free variables but not variables bound by assignment" in {
    val x = new Variable("x", None, Real)
    AlphaConversionHelper.replaceFree("[x:=2+x;]x>0".asFormula)(x, CDot) should be (
      BoxModality(Assign(x, Add(Real, Number(2), CDot)), GreaterThan(Real, x, Number(0))))
  }

  it should "rename free variables but not variables bound by ODEs" in {
    val x = new Variable("x", None, Real)
    val z = new Variable("z", None, Real)
    AlphaConversionHelper.replaceFree("[z'=2+x;](x>0 & z>0)".asFormula)(x, CDot) should be (
      BoxModality(ContEvolveProduct(NFContEvolve(Nil, Derivative(Real, z), Add(Real, Number(2), CDot), True)),
        And(GreaterThan(Real, CDot, Number(0)), GreaterThan(Real, z, Number(0)))))
  }

  it should "not rename variables bound by assignments in loops" in {
    val x = new Variable("x", None, Real)
    AlphaConversionHelper.replaceFree("[{x:=x+1;}*;]x>0".asFormula)(x, CDot) should be (
      BoxModality(Loop(Assign(x, Add(Real, x, Number(1)))),
        GreaterThan(Real, x, Number(0))))
  }

  it should "rename free variables but not bound variables in loops" in {
    val x = new Variable("x", None, Real)
    val z = new Variable("z", None, Real)
    AlphaConversionHelper.replaceFree("[{x:=x+1; ?z>5}*;](x>0 & z>4)".asFormula)(x, CDot) should be (
      BoxModality(Loop(Sequence(Assign(x, Add(Real, x, Number(1))), Test(GreaterThan(Real, z, Number(5))))),
        And(GreaterThan(Real, x, Number(0)), GreaterThan(Real, z, Number(4)))))
    AlphaConversionHelper.replaceFree("[{x:=x+1; ?z>5}*;](x>0 & z>4)".asFormula)(z, CDot) should be (
      BoxModality(Loop(Sequence(Assign(x, Add(Real, x, Number(1))), Test(GreaterThan(Real, CDot, Number(5))))),
        And(GreaterThan(Real, x, Number(0)), GreaterThan(Real, CDot, Number(4)))))
  }

  it should "rename free variables not mentioned in loops" in {
    val x = new Variable("x", None, Real)
    val z = new Variable("z", None, Real)
    AlphaConversionHelper.replaceFree("[{x:=x+1;}*;](x>0 & z>4)".asFormula)(x, CDot) should be (
      BoxModality(Loop(Assign(x, Add(Real, x, Number(1)))),
        And(GreaterThan(Real, x, Number(0)), GreaterThan(Real, z, Number(4)))))
    AlphaConversionHelper.replaceFree("[{x:=x+1;}*;](x>0 & z>4)".asFormula)(z, CDot) should be (
      BoxModality(Loop(Assign(x, Add(Real, x, Number(1)))),
        And(GreaterThan(Real, x, Number(0)), GreaterThan(Real, CDot, Number(4)))))
  }
}
