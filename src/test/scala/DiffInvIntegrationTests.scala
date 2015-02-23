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

  def runDiffInv(f : Formula) = {
    val node = helper.formulaToNode(f)
    helper.runTactic(helper.positionTacticToTactic(ODETactics.diffInvariantT), node)
    helper.report(node)
    node
  }


  "diff inv tactic" should "work" in {
    val f = "[x' = y, y' = x & x^2 + y^2 = 4;]1=1".asFormula
    val n = runDiffInv(f)
    fail()
    // TODO check expected result
  }

  "Diff inv system intro" should "introduce marker and prime postcondition" in {
    val s = sucSequent("[x'=x & x>3, y'=x & y>2 & z<0;]y>0".asFormula)
    val tactic = locateSucc(diffInvariantSystemIntroT)
    getProofSequent(tactic, new RootNode(s)) should be (
      sucSequent("y>0 & [$$x'=x & x>3, y'=x & y>2&z<0$$;](y>0)'".asFormula))
  }

  "Diff inv system head" should "pull out first ODE from marked system" in {
    val s = sucSequent("[$$x'=x & x>3, y'=x & y>2 & z<0$$;](y>0)'".asFormula)
    val tactic = locateSucc(diffInvariantSystemHeadT)
    getProofSequent(tactic, new RootNode(s)) should be (
      // [$$c, x' ≚ f(?) & H(?)$$;][x' := f(?);](H(?) -> p(?))
      sucSequent("[$$y'=x & y>2&z<0, x' ≚ x & x>3$$;][x':=x;](x>3 -> (y>0)')".asFormula))
  }

  it should "pull out first ODE from marked system repeatedly" in {
    val s = sucSequent("[$$x'=x & x>3, y'=x & y>2 & z<0$$;](y>0)'".asFormula)
    val tactic = locateSucc(diffInvariantSystemHeadT)
    val node = helper.runTactic(tactic, new RootNode(s))
    node.openGoals().foreach(_.sequent should be (
      // [$$c, x' ≚ f(?) & H(?)$$;][x' := f(?);](H(?) -> p(?))
      sucSequent("[$$y'=x & y>2&z<0, x' ≚ x & x>3$$;][x':=x;](x>3 -> (y>0)')".asFormula)))

    val secondNode = helper.runTactic(tactic, node.openGoals().head)
    secondNode.openGoals().foreach(_.sequent should be (
      sucSequent("[$$x' ≚ x & x>3, y' ≚ x & y>2&z<0$$;][y':=x;](y>2&z<0 -> [x':=x;](x>3 -> (y>0)'))".asFormula)))
  }
}
