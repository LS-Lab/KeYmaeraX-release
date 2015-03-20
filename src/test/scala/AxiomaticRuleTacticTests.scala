import edu.cmu.cs.ls.keymaera.core.{RootNode, Mathematica, KeYmaera}
import edu.cmu.cs.ls.keymaera.tactics.{AxiomaticRuleTactics, Interpreter, Tactics}
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.StringConverter._
import testHelper.SequentFactory._

import scala.collection.immutable.Map

/**
 * Created by smitsch on 3/16/15.
 * @author Stefan Mitsch
 */
class AxiomaticRuleTacticTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  // TODO mathematica is only necessary because of ProofFactory -> make ProofFactory configurable

  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig : Map[String, String] = Map("linkName" -> "/Applications/Mathematica.app/Contents/MacOS/MathKernel")

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

  "Box congruence" should "congruence rewrite with primes" in {
    val s = sucSequent("[x':=1;](x*y())'<=0 <-> [x':=1;]x'*y()<=0".asFormula)
    val tactic = AxiomaticRuleTactics.boxCongruenceT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "(x*y())'<=0 <-> x'*y()<=0".asFormula
  }

  "Diamond congruence" should "congruence rewrite with primes" in {
    val s = sucSequent("<x':=1;>(x*y())'<=0 <-> <x':=1;>x'*y()<=0".asFormula)
    val tactic = AxiomaticRuleTactics.diamondCongruenceT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "(x*y())'<=0 <-> x'*y()<=0".asFormula
  }

  "Box monotone" should "work" in {
    val s = sequent(Nil, "[x:=1;]x>0".asFormula :: Nil, "[x:=1;]x>-1".asFormula :: Nil)
    val tactic = AxiomaticRuleTactics.boxMonotoneT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x>0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>-1".asFormula
  }

  "Diamond monotone" should "work" in {
    val s = sequent(Nil, "<x:=1;>x>0".asFormula :: Nil, "<x:=1;>x>-1".asFormula :: Nil)
    val tactic = AxiomaticRuleTactics.diamondMonotoneT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x>0".asFormula
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>-1".asFormula
  }

  "Goedel" should "work" in {
    val s = sucSequent("[x:=1;]x>0".asFormula)
    val tactic = AxiomaticRuleTactics.goedelT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>0".asFormula
  }

  "Forall generalization" should "work" in {
    val s = sucSequent("\\forall x . x>0".asFormula)
    val tactic = AxiomaticRuleTactics.forallGeneralizationT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>0".asFormula
  }

  it should "alpha rename" in {
    val s = sucSequent("\\forall y . y>0".asFormula)
    val tactic = AxiomaticRuleTactics.forallGeneralizationT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "y>0".asFormula
  }

  "Forall congruence" should "work" in {
    val s = sucSequent("(\\forall x. x>5) <-> (\\forall x . x>0)".asFormula)
    val tactic = AxiomaticRuleTactics.forallCongruenceT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>5 <-> x>0".asFormula
  }

  it should "alpha rename" in {
    val s = sucSequent("(\\forall y. y>5) <-> (\\forall y. y>0)".asFormula)
    val tactic = AxiomaticRuleTactics.forallCongruenceT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "y>5 <-> y>0".asFormula
  }

  "Exists congruence" should "work" in {
    val s = sucSequent("(\\exists x. x>5) <-> (\\exists x . x>0)".asFormula)
    val tactic = AxiomaticRuleTactics.existsCongruenceT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>5 <-> x>0".asFormula
  }

  "Exists congruence" should "alpha rename" in {
    val s = sucSequent("(\\exists y. y>5) <-> (\\exists y. y>0)".asFormula)
    val tactic = AxiomaticRuleTactics.existsCongruenceT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "y>5 <-> y>0".asFormula
  }

  "Imply congruence" should "work" in {
    val s = sucSequent("(x>5 -> x>2) <-> (x>5 -> x>0)".asFormula)
    val tactic = AxiomaticRuleTactics.implyCongruenceT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>2 <-> x>0".asFormula
  }

  "Equiv congruence" should "work" in {
    val s = sucSequent("(x>5 <-> x>2) <-> (x>5 <-> x>0)".asFormula)
    val tactic = AxiomaticRuleTactics.equivCongruenceT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>2 <-> x>0".asFormula
  }

  "And congruence" should "work" in {
    val s = sucSequent("(x>5 & x>2) <-> (x>5 & x>0)".asFormula)
    val tactic = AxiomaticRuleTactics.andCongruenceT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>2 <-> x>0".asFormula
  }

  "Or congruence" should "work" in {
    val s = sucSequent("(x>5 | x>2) <-> (x>5 | x>0)".asFormula)
    val tactic = AxiomaticRuleTactics.orCongruenceT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>2 <-> x>0".asFormula
  }

  "Not congruence" should "work" in {
    val s = sucSequent("(!x>2) <-> (!x>0)".asFormula)
    val tactic = AxiomaticRuleTactics.notCongruenceT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>2 <-> x>0".asFormula
  }
}
