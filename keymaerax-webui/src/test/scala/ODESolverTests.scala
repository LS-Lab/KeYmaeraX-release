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
    val tactic = locateSucc(ImplyRightT) & LogicalODESolver.solveT(SuccPos(0))
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
    node.openGoals().last.sequent.succ.last shouldBe (
      "[{v' = a, x' = v & t >= 0}]x>0".asFormula
      )
  }

  "Inverse Ghost" should "work when we don't have to reorder diffeq" in {
    val f = "\\exists x ([{x' = 0*x + v, v' = 0*v + a, t' = 0*t + 1 & true & t >= 0}]x>0)".asFormula
    println(ODETactics.InverseDiffAuxHelpers.axiomInstance(f).prettyString)
    val node = helper.formulaToNode(f)
    val tactic = ODETactics.inverseDiffAuxiliaryT(SuccPos(0))
    helper.runTactic(tactic, node)
    node.openGoals().length shouldBe 1
    node.openGoals().last.sequent.succ.length shouldBe 1
    node.openGoals().last.sequent.succ.last shouldBe (
        "[{v' = 0*v + a, t' = 0*t + 1 & true & t >= 0}]x>0".asFormula)
  }

  it should "then work on v as well" in {
    val f = "\\exists x ([{v' = 0*v + a, t' = 0*t + 1 & true & t >= 0}]x>0)".asFormula
    val node = helper.formulaToNode(f)
    val tactic = ODETactics.inverseDiffAuxiliaryT(SuccPos(0))
    helper.runTactic(tactic, node)
    node.openGoals().length shouldBe 1
    node.openGoals().last.sequent.succ.length shouldBe 1
    node.openGoals().last.sequent.succ.last shouldBe (
      "[{t' = 0*t + 1 & true & t >= 0}]x>0".asFormula)
  }

  it should "not work when time is all that's left" in {
    ???
  }

  it should "playground" in {
    val formula = "[{x' = 0, y' = 0 & 1=1}]x=1"

    val f = KeYmaeraXParser.formulaParser(formula)

    val s = Sequent(
      scala.collection.immutable.Seq(),
      scala.collection.immutable.IndexedSeq(),
      scala.collection.immutable.IndexedSeq(f)
    )
    val pie = PosInExpr(0 :: 0 :: Nil)
    val asdf = TacticHelper.getTerm(s, SuccPosition(0, pie))
    println(asdf.prettyString)
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
  }
}
