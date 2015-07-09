/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
import edu.cmu.cs.ls.keymaerax.tactics.SearchTacticsImpl.locateSucc
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tactics.PropositionalTacticsImpl.{cohide2T,hideT,kModalModusPonensT,modusPonensT}
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaera, Mathematica}
import testHelper.ProvabilityTestHelper
import org.scalatest.{FlatSpec, Matchers, BeforeAndAfterEach}
import testHelper.ProofFactory._
import testHelper.SequentFactory._
import testHelper.StringConverter._

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
}
