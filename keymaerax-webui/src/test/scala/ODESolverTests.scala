/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics._
import org.scalatest.{PrivateMethodTester, FlatSpec, Matchers}
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary._

import scala.collection.immutable

/**
 * @author Nathan Fulton
 * Created by nfulton on 4/23/15.
 */
class ODESolverTests extends TacticTestSuite with PrivateMethodTester {
  //Useful values used throughout these tests.
  val nov    = Variable("doesnotoccur", None, Real)
  val acc    = Variable("acc", None, Real) //oh wow Matchers has a publicly exposed variable named a...
  val v      = Variable("v", None, Real)
  val x      = Variable("x", None, Real)
  val xPrime = DifferentialSymbol(x)
  val t      = Variable("t", None, Real)
  val tPrime = DifferentialSymbol(t)
  val five   = Number(5)
  val two    = Number(2)
  val one    = Number(1)
  val zero   = Number(0)

  private def getOde(s : String) = s.asFormula.asInstanceOf[Box].program.asInstanceOf[DifferentialProgram]

  "Weak Logical ODE Solver" should "work when time is explicit" in {
    val f = "x = 0 & v = 1 & a = 5 & t=0 -> [{x' =v, v' = a, t' = 0*t+1}]x >= 0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = locateSucc(ImplyRightT) & LogicalODESolver.weakSolveT(SuccPos(0))
    helper.runTactic(tactic, node)
    helper.report(node)
    node shouldBe 'closed
  }

  ignore should "work when time is implicit" in {
    val f = "x = 0 & v = 1 & a = 5 -> [{x' =v, v' = a}]x >= 0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = locateSucc(ImplyRightT) & LogicalODESolver.weakSolveT(SuccPos(0))
    helper.runTactic(tactic, node)
    helper.report(node)
    node shouldBe 'closed
  }

  /**
   * @author Nathan Fulton
   *         @todo Nathan
   */
  ignore should "work if there's already a time in the ODE and it's not in explicit linear form" in {
    val f = "x = 0 & v = 1 & a = 5 & t=0 -> [{x' =v, v' = a, t' = 1}]x >= 0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = locateSucc(ImplyRightT) & LogicalODESolver.weakSolveT(SuccPos(0))
    helper.runTactic(tactic, node)
    helper.report(node)
    node shouldBe 'closed
  }

  /**
   * @author Nathan Fulton
   *         @todo Nathan
   */
  ignore should "work when we have two separate sets of linear vars." in {
    val f = "x = 0 & v = 1 & a = 5 & t=0 & w = 0 & z = 0 -> [{x' =v, v' = a, w' = z, t' = 1}]x >= 0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = locateSucc(ImplyRightT) & LogicalODESolver.weakSolveT(SuccPos(0))
    helper.runTactic(tactic, node)
    helper.report(node)
    node shouldBe 'closed
  }

  /**
   * @author Nathan Fulton
   */
  "Logical ODE Solver" should "work when time is explicit" in {
    val f = "x = 0 & v = 1 & a = 5 & t=0 -> [{x' =v, v' = a, t' = 0*t+1}]x >= 0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = locateSucc(ImplyRightT) & LogicalODESolver.solveT(SuccPos(0))
    helper.runTactic(tactic, node)
    helper.report(node)
//    node shouldBe 'closed @todo
  }

  /**
   * @author Nathan Fulton
   */
  ignore should "work when time is implicit" in {
    val f = "x = 0 & v = 1 & a = 5 -> [{x' =v, v' = a}]x >= 0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = locateSucc(ImplyRightT) & LogicalODESolver.solveT(SuccPos(0))
    helper.runTactic(tactic, node)
    helper.report(node)
    node shouldBe 'closed
  }

  //@todo Nathan
  ignore should "work with ACAS X input" in {
    val ante = "(w()=-1|w()=1)&\\forall t \\forall ro \\forall ho (0<=t&t < w()*(dhf()-dhd)/a()&ro=rv()*t&ho=w()*a()/2*t^2+dhd*t|t>=0&t>=w()*(dhf()-dhd)/a()&ro=rv()*t&(w()*(dhf()-dhd)<=0&ho=dhf()*t|w()*(dhf()-dhd)>0&ho=dhf()*t-w()*(w()*(dhf()-dhd))^2/(2*a()))->r-ro < -rp|r-ro>rp|w()*h < w()*ho-hp)&(hp>0&rp>0&rv()>=0&a()>0)".asFormula
    val succ = "[{r'=-rv(),dhd'=ao(),h'=-dhd&w()*dhd>=w()*dhf()|w()*ao()>=a()}]((w()=-1|w()=1)&\\forall t \\forall ro \\forall ho (0<=t&t < w()*(dhf()-dhd)/a()&ro=rv()*t&ho=w()*a()/2*t^2+dhd*t|t>=0&t>=w()*(dhf()-dhd)/a()&ro=rv()*t&(w()*(dhf()-dhd)<=0&ho=dhf()*t|w()*(dhf()-dhd)>0&ho=dhf()*t-w()*(w()*(dhf()-dhd))^2/(2*a()))->r-ro < -rp|r-ro>rp|w()*h < w()*ho-hp)&(hp>0&rp>0&rv()>=0&a()>0))".asFormula
    val s = Sequent(Nil, immutable.IndexedSeq(ante), immutable.IndexedSeq(succ))
    val tactic = LogicalODESolver.solveT(SuccPos(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    // TODO expected succedent
    result.openGoals().head.sequent.succ should contain only "true".asFormula
  }
}

class InverseDiffGhostTests extends TacticTestSuite {
  "Comma Commute Axiom" should "work on a binary example" in {
    val f = "[{x' = v, v' = a & t >= 0}]x>0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = ODETactics.commaCommuteT(SuccPos(0))
    helper.runTactic(tactic, node)
    node.openGoals().length shouldBe 1
    node.openGoals().last.sequent.succ.length shouldBe 1
    node.openGoals().last.sequent.succ.last shouldBe
      "[{v' = a, x' = v & t >= 0}]x>0".asFormula

  }

  "Inverse Ghost" should "work when we don't have to reorder diffeq" in {
    val f = "\\exists x ([{x' = 0*x+v, v' = 0*v + a, t' = 0*t + 1 & true & t >= 0}]x>0)".asFormula
//    println(ODETactics.SystemHelpers.axiomInstance(f).prettyString)
    val node = helper.formulaToNode(f)
    val tactic = ODETactics.inverseDiffAuxiliaryT(SuccPos(0))
    helper.runTactic(tactic, node)
    node.openGoals().length shouldBe 1
    node.openGoals().last.sequent.succ.length shouldBe 1
    node.openGoals().last.sequent.succ.last shouldBe
      "[{v' = 0*v + a, t' = 0*t + 1 & true & t >= 0}]x>0".asFormula
  }


  it should "then work on v as well" in {
    val f = "\\exists x ([{v' = 0*v + a, t' = 0*t + 1 & true & t >= 0}]x>0)".asFormula
    val node = helper.formulaToNode(f)
    val tactic = ODETactics.inverseDiffAuxiliaryT(SuccPos(0))
    helper.runTactic(tactic, node)
    node.openGoals().length shouldBe 1
    node.openGoals().last.sequent.succ.length shouldBe 1
    node.openGoals().last.sequent.succ.last shouldBe
      "[{t' = 0*t + 1 & true & t >= 0}]x>0".asFormula
  }

  it should "not work when time is all that's left" in {
    ???
  }

//  it should "playground" in {
//    val formula = "[{x' = 0, y' = 0 & 1=1}]x=1"
//
//    val f = KeYmaeraXParser.formulaParser(formula)
//
//    val s = Sequent(
//      scala.collection.immutable.Seq(),
//      scala.collection.immutable.IndexedSeq(),
//      scala.collection.immutable.IndexedSeq(f)
//    )
//    val pie = PosInExpr(0 :: 0 :: Nil)
//    val asdf = TacticHelper.getTerm(s, SuccPosition(0, pie))
//    println(asdf.prettyString)
//  }
//
  /**
   * The Lipschitz axiom tactic depends on this assumption.
   * @author Nathan Fulton
   */
  "Compose" should "be right assoc" in {
    val formula = "[x := 0; y := 1; x:=2;]1=1".asFormula

    formula.asInstanceOf[Box].program.asInstanceOf[Compose].left.asInstanceOf[Assign].x shouldBe Variable("x", None, Real)
  }
}

class InverseDiffCutTests extends TacticTestSuite {
  ////
  // Inverse Cut Tests
  ///

  /*
   * And Reodering derived axiom
   * This axiom is used to move the x=blah to the end of the evolution domain constraint so that DC
   * uses the correct thing.
   */
  "And Reodering" should "move the last element of a conjunction to the front." in {
    val f = "[{x'=v,v'=a & (true & v=v_0 + a*t & x = x_0 + (a/2)*t^2 + v_0*t & t >= 0)}]x > 0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = LogicalODESolver.AndReoderingT(SuccPos(0))
    helper.runTactic(tactic, node)
    node.openGoals().length shouldBe 1
    node.openGoals().last.sequent.succ.length shouldBe 1
    node.openGoals().last.sequent.succ.last shouldBe (
      "[{x'=v,v'=a & t >= 0 & (true & v=v_0 + a*t & x = x_0 + (a/2)*t^2 + v_0*t)}]x > 0".asFormula)
  }

  "Inverse cut" should "work when we don't have to reorder initial conjunction" in {
    val f = "[{x'=v,v'=a & (true & v=v_0 + a*t & x = x_0 + (a/2)*t^2 + v_0*t)}]x > 0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = ODETactics.diffInverseCutT(SuccPos(0))
    helper.runTactic(tactic,node)
    helper.report(node)
    //@todo
    fail("No assertions -- this test isn't complete yet.")
  }
}

class ODESolutionTactic extends TacticTestSuite {

  "->" should "default to correct assoc" in {
    "1=1 -> 2=2 -> 3=3".asFormula shouldBe "1=1 -> (2=2 -> 3=3)".asFormula
  }

  "ODE solver" should "work for example in US paper" in {
    val f = "[{b' = 1}](x_0 + (a/2)*b^2 + v_0*b >= 0)".asFormula
    val node = helper.formulaToNode(f)
    val tactic = ODETactics.diffSolveConstraintT(SuccPos(0))
    helper.runTactic(tactic,node)
    helper.report(node)
    fail("No assertion.")
  }

  "Diff. Solution tactic" should "solve simplest case ODEsolve" in { /* works */
    val s = testHelper.SequentFactory.sequent(Nil, "r>=0".asFormula :: Nil, "[{r' = 0}](r>=0)".asFormula :: Nil)
    val tactic = debugT("here") & locateSucc(ODETactics.diffSolution(None)) & debugT("there")
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
  }

  "Diff. Solution tactic" should "solve simplest case ODEsolve with 1" in { /* doesn't work */
    /* Stefan: the r'=1 is taken as time and something goes wrong with that */
  val s = testHelper.SequentFactory.sequent(Nil, "r>=0".asFormula :: Nil, "[{r' = 1}](r>=0)".asFormula :: Nil)
    val tactic = debugT("here") & locateSucc(ODETactics.diffSolution(None)) & debugT("there")
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
  }


  "Diff. Solution tactic" should "solve simplest case ODEsolve with 2" in { /* works */
  val s = testHelper.SequentFactory.sequent(Nil, "r>=0".asFormula :: Nil, "[{r' = 2}](r>=0)".asFormula :: Nil)
    val tactic = debugT("here") & locateSucc(ODETactics.diffSolution(None)) & debugT("there")
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
  }

  it should "solve simplest using max (minimal)" in { /* works */
  val s = testHelper.SequentFactory.sequent(Nil, "max(0,r)=r".asFormula :: Nil, "[{r' = 0}](r>=0)".asFormula :: Nil)
    val tactic = debugT("here") & locateSucc(ODETactics.diffSolution(None, TactixLibrary.la(hideT, "max(0,r)=r"))) & debugT("there")
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
  }

  it should "solve simplest using max (with abbreviation)" in { /* works */
  val s = testHelper.SequentFactory.sequent(Nil, "max(0,r)=r".asFormula :: Nil, "[{r' = 0}](r>=0)".asFormula :: Nil)
    val tactic = EqualityRewritingImpl.abbrv(Variable("max0"))(AntePosition(0).first) &
      debugT("here") & locateSucc(ODETactics.diffSolution(None, TactixLibrary.la(hideT, "max0=max(0,r)"))) & debugT("there")
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
  }

  it should "solve simplest using max (with abbreviation and hide)" in { /* works but pointless */
  val s = testHelper.SequentFactory.sequent(Nil, "max(0,r)=r".asFormula :: Nil, "[{r' = 0}](r>=0)".asFormula :: Nil)
    val tactic = EqualityRewritingImpl.abbrv(Variable("max0"))(AntePosition(0).first) & hideT(AntePosition(0)) &
      debugT("here") & locateSucc(ODETactics.diffSolution(None)) & debugT("there")
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
  }

  it should "solve simplest using max (with MinMaxT)" in { /* works but only by decomposing Max */
  val s = testHelper.SequentFactory.sequent(Nil, "max(0,r)=r".asFormula :: Nil, "[{r' = 0}](r>=0)".asFormula :: Nil)
    val tactic = ArithmeticTacticsImpl.MinMaxT(AntePosition(0, PosInExpr(0 :: Nil))) &
      debugT("here") & locateSucc(ODETactics.diffSolution(None)) & debugT("there")
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
  }

  it should "solve simplest using max (with MinMaxT and cut -- kind of a hack)" in { /* works but kind of a hack */
  val s = testHelper.SequentFactory.sequent(Nil, "max(0,r)=r".asFormula :: Nil, "[{r' = 0}](r>=0)".asFormula :: Nil)
    val tactic = ArithmeticTacticsImpl.MinMaxT(AntePosition(0, PosInExpr(0 :: Nil))) &
      locateSucc(ODETactics.diffSolution(None)) & debugT("here") &
      cutT(Some("max(0,r)=max_0".asFormula)) & SearchTacticsImpl.onBranch(
        (BranchLabels.cutShowLbl, debugT("show") &
          ArithmeticTacticsImpl.MinMaxT(SuccPosition(1, PosInExpr(0 :: Nil))) &
          arithmeticT),
        (BranchLabels.cutUseLbl, debugT("use") & locateAnte(eqLeft(exhaustive=true)) &
          TacticLibrary.hideT(AntePosition(5)) & // "0>=r&r=0|0 < r&r=r"
          TacticLibrary.hideT(AntePosition(0)) & // "max_0=r"
          debugT("done"))
      )
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
  }

  /* Other non-minimal tests */
  it should "solve simplest using max" in { /* works */
  val s = testHelper.SequentFactory.sequent(Nil, "max(0,r)=r".asFormula :: Nil, "[{r' = 0}](max(0,r)=r)".asFormula :: Nil)
    val tactic = debugT("here") & locateSucc(ODETactics.diffSolution(None, TactixLibrary.la(hideT, "max(0,r)=r"))) & debugT("there")
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
  }

  it should "solve simplest using max 2" in { /* works */
  val s = testHelper.SequentFactory.sequent(Nil, "r>=0".asFormula :: Nil, "[{r' = 0}](max(0,r)=r)".asFormula :: Nil)
    val tactic = debugT("here") & locateSucc(ODETactics.diffSolution(None)) & debugT("there")
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
  }
}

class GhostOfLipschitz extends TacticTestSuite {
  "Inverse Lipschitz ghost" should "work on simple example" in {
    //Make sure things occur free and bound and such a lot.
    //@todo changing v to y creates a clash...
    val f = "\\exists x [{x'=0*x + v, v' = 0*v + a, t' = 1 & t > 0 & x>0 & v>0}]x>0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = ODETactics.inverseLipschitzGhostT(SuccPos(0)) & SearchTacticsImpl.onBranch(
      (BranchLabels.cutShowLbl, debugT("This is the cut show branch")),
      (BranchLabels.cutUseLbl, debugT("This is the cut use brnach"))
    )
    helper.runTactic(tactic,node)
    helper.report(node)
  }

  ignore should "not clash because of error caused by y in axiom file." in {
    val f = "\\exists x [{x'=0*x + y, y' = 0*y + a, t' = 1 & t > 0 & x>0 & y>0}]x>0".asFormula
    val node = helper.formulaToNode(f)
    val tactic = ODETactics.inverseLipschitzGhostT(SuccPos(0))
    helper.runTactic(tactic,node)
    helper.report(node)
  }
}

class DGPlusPlus extends TacticTestSuite {
  "DG++" should "work when no variables are different" in {
    val f = "\\forall y [{y' = x*v, x' = z, h' = -y, t' = 0*t + 1 & x=  0 & y = 0 & a=0 & t=0}]1=1".asFormula //nonsense
    val node = helper.formulaToNode(f)
    val tactic = edu.cmu.cs.ls.keymaerax.tactics.ODETactics.DiffGhostPlusPlusSystemT(SuccPos(0))
    helper.runTactic(tactic, node)
    node.openGoals().length shouldBe 1
    node.openGoals().last.sequent.succ.last shouldBe "[{x' = z, h' = -y, t' = 0*t + 1 & x=  0 & y = 0 & a=0 & t=0}]1=1".asFormula
  }

  it should "work for ACAS X system after a , commute" in {
    val f = "\\forall r [{r'=-rv(), dhd'=ao(), h'=-dhd, t'=0*t+1 & 1=1}]2=2".asFormula //nonsense
    val node = helper.formulaToNode(f)
    val tactic = edu.cmu.cs.ls.keymaerax.tactics.ODETactics.DiffGhostPlusPlusSystemT(SuccPos(0))
    helper.runTactic(tactic, node)
    node.openGoals().length shouldBe 1
    node.openGoals().last.sequent.succ.last shouldBe "[{dhd'=ao(), h'=-dhd, t'=0*t+1 & 1=1}]2=2".asFormula
  }
}
