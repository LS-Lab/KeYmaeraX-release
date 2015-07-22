/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.locateSucc
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl.{cohide2T, ConsolidateSequentT, hideT, ImplyToAndT,
  kModalModusPonensT, modusPonensT}
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaera, Mathematica}
import testHelper.ProvabilityTestHelper
import org.scalatest.{FlatSpec, Matchers, BeforeAndAfterEach}
import testHelper.ProofFactory._
import testHelper.SequentFactory._

import scala.collection.immutable.Map

/**
 * Created by smitsch on 2/20/15.
 * @author Stefan Mitsch
 */
class PropositionalTacticTests extends FlatSpec with Matchers with BeforeAndAfterEach {

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
    Tactics.MathematicaScheduler = null
    Tactics.KeYmaeraScheduler = null
  }

  "K Modal Modus Ponens" should "be [x:=2;](x>1 -> x>0) on [x:=2;]x>1 -> [x:=2;]x>0" in {
    val tactic = locateSucc(kModalModusPonensT)
    getProofSequent(tactic, new RootNode(sucSequent("[x:=2;]x>1 -> [x:=2;]x>0".asFormula))) should be (
      sucSequent("[x:=2;](x>1 -> x>0)".asFormula))
  }

  "Modus ponens" should "work when assumption comes after implication" in {
    val tactic = modusPonensT(AntePosition(1), AntePosition(0))
    getProofSequent(tactic, new RootNode(sequent(Nil, "x>5 -> x>3".asFormula :: "x>5".asFormula :: Nil, Nil))) should be (
      sequent(Nil, "x>3".asFormula :: Nil, Nil))
  }

  it should "work when assumption comes before implication" in {
    val tactic = modusPonensT(AntePosition(0), AntePosition(1))
    getProofSequent(tactic, new RootNode(sequent(Nil, "x>5".asFormula :: "x>5 -> x>3".asFormula :: Nil, Nil))) should be (
      sequent(Nil, "x>3".asFormula :: Nil, Nil))
  }

  "Cohide2" should "hide everything except the specified positions" in {
    val tactic = cohide2T(AntePosition(1), SuccPosition(1))
    val s = sequent(Nil,
      "a>0".asFormula :: "b>1".asFormula :: "c>2".asFormula :: Nil,
      "x>0".asFormula :: "y>1".asFormula :: "z>2".asFormula :: Nil)
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "b>1".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "y>1".asFormula
  }

  it should "hide nothing when the only positions present are the ones to retain" in {
    val tactic = cohide2T(AntePosition(0), SuccPosition(0))
    val s = sequent(Nil,
      "a>0".asFormula :: Nil,
      "x>0".asFormula :: Nil)
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "a>0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>0".asFormula
  }

  it should "set the continuation correctly" in {
    // TODO mock testing
    val tactic = cohide2T(AntePosition(0), SuccPosition(0)) & hideT(AntePosition(0))
    val s = sequent(Nil,
      "a>0".asFormula :: Nil,
      "x>0".asFormula :: Nil)
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>0".asFormula
  }

  it should "not be applicable when positions do not point to antecedent and succedent" in {
    val s = sequent(Nil,
      "a>0".asFormula :: "b>1".asFormula :: "c>2".asFormula :: Nil,
      "x>0".asFormula :: "y>1".asFormula :: "z>2".asFormula :: Nil)
    cohide2T(AntePosition(1), AntePosition(2)).applicable(new RootNode(s)) shouldBe false
    cohide2T(SuccPosition(1), SuccPosition(2)).applicable(new RootNode(s)) shouldBe false
  }

  it should "not be applicable when positions point outside the sequent" in {
    val s = sequent(Nil,
      "a>0".asFormula :: "b>1".asFormula :: "c>2".asFormula :: Nil,
      "x>0".asFormula :: "y>1".asFormula :: "z>2".asFormula :: Nil)
    cohide2T(AntePosition(5), SuccPosition(1)).applicable(new RootNode(s)) shouldBe false
    cohide2T(AntePosition(1), SuccPosition(5)).applicable(new RootNode(s)) shouldBe false
  }

  "Consolidate sequent" should "consolidate sequent from simple formulas" in {
    val s = sequent(Nil, "x>0".asFormula :: Nil, "y<0".asFormula :: Nil)
    val result = helper.runTactic(ConsolidateSequentT, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante shouldBe empty
    result.openGoals().head.sequent.succ should contain only "x>0 -> y<0".asFormula
  }

  it should "consolidate sequent from many formulas" in {
    val s = sequent(Nil, "xa>0".asFormula :: "xb>1".asFormula :: "xc>2".asFormula :: Nil, "ya<0".asFormula :: "yb<1".asFormula :: "yc<2".asFormula :: Nil)
    val result = helper.runTactic(ConsolidateSequentT, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante shouldBe empty
    result.openGoals().head.sequent.succ should contain only "xa>0&xb>1&xc>2 -> ya<0|yb<1|yc<2".asFormula
  }

  it should "consolidate sequent from many formulas (containing conjunctions and disjunctions)" in {
    val s = sequent(Nil, "xa>0".asFormula :: "xb>1".asFormula :: "xc>2&xd>3".asFormula :: Nil, "ya<0|yc<2".asFormula :: "yb<1".asFormula :: Nil)
    val result = helper.runTactic(ConsolidateSequentT, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante shouldBe empty
    result.openGoals().head.sequent.succ should contain only "xa>0&xb>1&(xc>2&xd>3) -> (ya<0|yc<2)|yb<1".asFormula
  }

  it should "consolidate sequent when antecedent is empty and succedent contains only 1 formula" in {
    val s = sequent(Nil, Nil, "ya<0".asFormula :: Nil)
    val result = helper.runTactic(ConsolidateSequentT, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante shouldBe empty
    result.openGoals().head.sequent.succ should contain only "ya<0".asFormula
  }

  it should "consolidate sequent when antecedent is empty" in {
    val s = sequent(Nil, Nil, "ya<0".asFormula :: "yb<1".asFormula :: Nil)
    val result = helper.runTactic(ConsolidateSequentT, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante shouldBe empty
    result.openGoals().head.sequent.succ should contain only "ya<0|yb<1".asFormula
  }

  it should "consolidate sequent when succedent is empty and antecedent contains only 1 formula" in {
    val s = sequent(Nil, "xa>0".asFormula :: Nil, Nil)
    val result = helper.runTactic(ConsolidateSequentT, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante shouldBe empty
    result.openGoals().head.sequent.succ should contain only "xa>0 -> !(xa>0)".asFormula
  }

  it should "consolidate sequent when succedent is empty" in {
    val s = sequent(Nil, "xa>0".asFormula :: "xb>1".asFormula :: "xc>2".asFormula :: Nil, Nil)
    val result = helper.runTactic(ConsolidateSequentT, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante shouldBe empty
    result.openGoals().head.sequent.succ should contain only "xa>0&xb>1&xc>2 -> !(xa>0&xb>1&xc>2)".asFormula
  }

  it should "consolidate sequent when both antecedent and succedent are empty" in {
    val s = sequent(Nil, Nil, Nil)
    val result = helper.runTactic(ConsolidateSequentT, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante shouldBe empty
    result.openGoals().head.sequent.succ shouldBe empty
  }

  "ImplyToAndT" should "rewrite an implication to a negated conjunction" in {
    val s = sucSequent("x>0->x>=0".asFormula)
    val result = helper.runTactic(locateSucc(ImplyToAndT), new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante shouldBe empty
    result.openGoals().head.sequent.succ should contain only "!(x>0&!x>=0)".asFormula
  }

  it should "rewrite an implication a->b to !(a&!b) with complicated a and b" in {
    val s = sucSequent("(x>0 & y<2 | z>5 -> x>7) -> (x>=0 & y<5 <-> z>8)".asFormula)
    val result = helper.runTactic(locateSucc(ImplyToAndT), new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante shouldBe empty
    result.openGoals().head.sequent.succ should contain only "!((x>0 & y<2 | z>5 -> x>7) & !(x>=0 & y<5 <-> z>8))".asFormula
  }

  it should "rewrite an implication to a negated conjunction in context" in {
    val s = sucSequent("[i:=5;](j>2 & (x>0->x>=0))".asFormula)
    val result = helper.runTactic(ImplyToAndT(SuccPosition(0, PosInExpr(List(1, 1)))), new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().head.sequent.ante shouldBe empty
    result.openGoals().head.sequent.succ should contain only "[i:=5;](j>2 & !(x>0&!x>=0))".asFormula
  }
}
