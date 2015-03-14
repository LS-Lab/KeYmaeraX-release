import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.ODETactics._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.{HybridProgramTacticsImpl, ODETactics}
import testHelper.ProofFactory._
import testHelper.SequentFactory._
import testHelper.StringConverter._

/**
 * Created by nfulton on 2/22/15.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class DiffInvIntegrationTests extends TacticTestSuite {

  "Assign" should "work" in {
    val f = "[a := 0;]a = 0".asFormula
    val node = helper.formulaToNode(f)
    helper.runTactic(helper.positionTacticToTactic(HybridProgramTacticsImpl.boxAssignT), node)
    helper.report(node)
    node.openGoals().flatMap(_.sequent.ante) should contain only "a_1=0".asFormula
    node.openGoals().flatMap(_.sequent.succ) should contain only "a_1=0".asFormula
  }

  "Diff Assign" should "work with 1 box" in {
    val f = "[a' := 1;]a'=1".asFormula
    val node = helper.formulaToNode(f)
    helper.runTactic(helper.positionTacticToTactic(HybridProgramTacticsImpl.boxDerivativeAssignT), node)
    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "1=1".asFormula
  }

  it should "work with 1 box and an unprimed occurance" in {
    val f = "[a' := 1;](a=1 -> a'=1)".asFormula
    val node = helper.formulaToNode(f)
    helper.runTactic(helper.positionTacticToTactic(HybridProgramTacticsImpl.boxDerivativeAssignT), node)
    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "a=1 -> 1=1".asFormula
  }

  it should "work with 2 boxes" in {
    import scala.language.postfixOps
    val f = "[a' := 1;](a>b -> [b' := 1;](true -> a'=b))'".asFormula
    val node = helper.formulaToNode(f)
    helper.runTactic(helper.positionTacticToTactic(HybridProgramTacticsImpl.boxDerivativeAssignT)*, node)
    node.openGoals().flatMap(_.sequent.ante) shouldBe empty
    node.openGoals().flatMap(_.sequent.succ) should contain only "(a>b -> [b':=1;](true -> 1=b))'".asFormula
  }

  "diff inv tactic" should "work" in {
    val s = sequent(Nil, "x>=0".asFormula::Nil, "[x' = 2;]x>=0".asFormula :: Nil)
    val t = locateSucc(ODETactics.diffInvariantT)
    val n = helper.runTactic(t, new RootNode(s))
    n shouldBe 'closed
    // without arithmetic tactic at the end:
//    n.openGoals().flatMap(_.sequent.ante) should contain only "x>=0".asFormula
//    n.openGoals().flatMap(_.sequent.succ) should contain only "!true | 2>=0".asFormula
  }

  it should "work with conjunction in inv" in {
    val s = sequent(Nil, "x>=0 & x>=x".asFormula::Nil, "[x' = 2;](x>=0 & x>=x)".asFormula :: Nil)
    val t = locateSucc(ODETactics.diffInvariantT)
    val n = helper.runTactic(t, new RootNode(s))
    n shouldBe 'closed
    // without arithmetic tactic at the end:
//    n.openGoals().flatMap(_.sequent.ante) should contain only "x>=0 & x>=x".asFormula
//    n.openGoals().flatMap(_.sequent.succ) should contain only "!true | (2>=0 & 2>=2)".asFormula
  }

  it should "work with disjunction in inv" in {
    val s = sequent(Nil, "x>=0 & x>=x".asFormula::Nil, "[x' = 2;](x>=0 | x>=x)".asFormula :: Nil)
    val t = locateSucc(ODETactics.diffInvariantT)
    val n = helper.runTactic(t, new RootNode(s))
    n shouldBe 'closed
    // without arithmetic tactic at the end:
//    n.openGoals().flatMap(_.sequent.ante) should contain only "x>=0 & x>=x".asFormula
//    n.openGoals().flatMap(_.sequent.succ) should contain only "!true | (2>=0 & 2>=2)".asFormula
  }

  it should "work with implication in inv" in {
    val s = sequent(Nil, "x>=0 -> x>=x".asFormula::Nil, "[x' = 2;](x>=0 -> x>=x)".asFormula :: Nil)
    val t = locateSucc(ODETactics.diffInvariantT)
    val n = helper.runTactic(t, new RootNode(s))
    n.openGoals().flatMap(_.sequent.ante) should contain only "x>=0 -> x>=x".asFormula
    n.openGoals().flatMap(_.sequent.succ) should contain only "2<=0 & 2>=2".asFormula
  }

  it should "derive constant symbols to 0" in {
    val s = sequent(Nil, "x>=0 & y()>=0".asFormula::Nil, "[x' = 2;](x>=0 & y()>=0)".asFormula :: Nil)
    val t = locateSucc(ODETactics.diffInvariantT)
    val n = helper.runTactic(t, new RootNode(s))
    // 2>=0 && 0>=0
    n shouldBe 'closed
  }

  it should "derive multiplication" in {
    val s = sequent(Nil, "x>=0 & y()>=0".asFormula::Nil, "[x' = 2;](x*y()>=0)".asFormula :: Nil)
    val t = locateSucc(ODETactics.diffInvariantT)
    val n = helper.runTactic(t, new RootNode(s))
    // x*0 + 2*y()>=0
    n shouldBe 'closed
  }

  it should "derive nested multiplication" in {
    val s = sequent(Nil, "x>=0 & y()>=0 & z>=0".asFormula::Nil, "[x' = 2, z'=1;](x*y()*z>=0)".asFormula :: Nil)
    val t = locateSucc(ODETactics.diffInvariantT)
    val n = helper.runTactic(t, new RootNode(s))
    // x*(0*z + y()*1) + 2*(y()*z)>=0
    n shouldBe 'closed
  }

  it should "derive division" in {
    val s = sequent(Nil, "x>=0 & y()>0".asFormula::Nil, "[x' = 2;](x/y()>=0)".asFormula :: Nil)
    val t = locateSucc(ODETactics.diffInvariantT)
    val n = helper.runTactic(t, new RootNode(s))
    // x*0 + 2*y()>=0
    n shouldBe 'closed
  }

  // infinite loop (might also be caused by pretty printer issue because nothing ever closes)
  ignore should "work with a complicated example" in {
    val s = sequent(Nil, Nil, "[x' = y, y' = x & x^2 + y^2 = 4;]1=1".asFormula::Nil)
    val t = locateSucc(ODETactics.diffInvariantT)
    val n = helper.runTactic(t, new RootNode(s))
    n.openGoals().flatMap(_.sequent.ante) shouldBe empty
    n.openGoals().flatMap(_.sequent.succ) should contain only "!(x^2+y^2=4) | [x':=y;](!true | 0=0)".asFormula
  }

  "Diff inv system intro" should "introduce marker and prime postcondition" in {
    val s = sucSequent("[x'=x, y'=x & y>2 & z<0;]y>0".asFormula)
    val tactic = locateSucc(diffInvariantSystemIntroT)
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("(y>2&z<0 -> y>0) & [$$x'=x, y'=x$$ & y>2&z<0;](y>0)'".asFormula))
  }

  "Diff inv system head" should "pull out first ODE from marked system" in {
    val s = sucSequent("[$$x'=x, y'=x $$ & y>2 & z<0;](y>0)'".asFormula)
    val tactic = locateSucc(diffInvariantSystemHeadT)
    getProofSequent(tactic, new RootNode(s)) should be (
      // [$$c, x' ≚ f(?) & H(?)$$;][x' := f(?);](H(?) -> p(?))
      sucSequent("[$$y'=x, x' ≚ x$$ & y>2&z<0;][x':=x;](y>0)'".asFormula))
  }

  it should "pull out first ODE from marked system repeatedly" in {
    val s = sucSequent("[$$x'=x, y'=x$$ & y>2 & z<0;](y>0)'".asFormula)
    val tactic = locateSucc(diffInvariantSystemHeadT)
    val node = helper.runTactic(tactic, new RootNode(s))
    node.openGoals().foreach(_.sequent should be (
      // [$$c, x' ≚ f(?) & H(?)$$;][x' := f(?);](H(?) -> p(?))
      sucSequent("[$$y'=x, x' ≚ x$$ & y>2&z<0;][x':=x;](y>0)'".asFormula)))

    val secondNode = helper.runTactic(tactic, node.openGoals().head)
    secondNode.openGoals().foreach(_.sequent should be (
      sucSequent("[$$x' ≚ x, y' ≚ x$$ & y>2&z<0;][y':=x;][x':=x;](y>0)'".asFormula)))
  }

  "Diff inv tail" should "remove marked ODE" in {
    val s = sucSequent("[$$x' ≚ x$$ & x>3;][x':=x;](x>0)'".asFormula)
    val tactic = locateSucc(diffInvariantSystemTailT)
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("[x':=x;](x>0)'".asFormula))
  }
}
