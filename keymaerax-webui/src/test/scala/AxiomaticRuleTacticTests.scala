import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaera, Mathematica}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import testHelper.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.SequentFactory._

import scala.collection.immutable.Map

/**
 * Created by smitsch on 3/16/15.
 * @author Stefan Mitsch
 */
class AxiomaticRuleTacticTests extends FlatSpec with Matchers with BeforeAndAfterEach {
  // TODO mathematica is only necessary because of ProofFactory -> make ProofFactory configurable

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

  "Box congruence" should "congruence rewrite with primes" in {
    val s = sucSequent("[x':=1;](x*y())'<=0 <-> [x':=1;]x'*y()<=0".asFormula)
    val tactic = AxiomaticRuleTactics.equivalenceCongruenceT(PosInExpr(1::Nil))

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "(x*y())'<=0 <-> x'*y()<=0".asFormula
  }

  "Diamond congruence" should "congruence rewrite with primes" in {
    val s = sucSequent("<x':=1;>(x*y())'<=0 <-> <x':=1;>x'*y()<=0".asFormula)
    val tactic = AxiomaticRuleTactics.equivalenceCongruenceT(PosInExpr(1::Nil))

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

  "Forall generalization" should "alpha rename if necessary" in {
    val s = sucSequent("\\forall y x>0".asFormula)
    val tactic = AxiomaticRuleTactics.forallGeneralizationT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>0".asFormula
  }

  ignore should "work on a simple example" in {
    val s = sucSequent("\\forall x x>0".asFormula)
    val tactic = AxiomaticRuleTactics.forallGeneralizationT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>0".asFormula
  }

  ignore should "alpha rename simple" in {
    val s = sucSequent("\\forall y y>0".asFormula)
    val tactic = AxiomaticRuleTactics.forallGeneralizationT

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "y>0".asFormula
  }

  "Forall congruence" should "work" in {
    val s = sucSequent("(\\forall x x>5) <-> (\\forall x x>0)".asFormula)
    val tactic = AxiomaticRuleTactics.equivalenceCongruenceT(PosInExpr(0::Nil))

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>5 <-> x>0".asFormula
  }

  it should "alpha rename" in {
    val s = sucSequent("(\\forall y y>5) <-> (\\forall y y>0)".asFormula)
    val tactic = AxiomaticRuleTactics.equivalenceCongruenceT(PosInExpr(0::Nil))

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "y>5 <-> y>0".asFormula
  }

  it should "alpha rename complicated" in {
    val s = sucSequent("(\\forall x [x:=2;]x>1) <-> (\\forall x [x:=2;]x>0)".asFormula)
    val tactic = AxiomaticRuleTactics.equivalenceCongruenceT(PosInExpr(0::Nil))

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "[x:=2;]x>1 <-> [x:=2;]x>0".asFormula
  }

  "Exists congruence" should "work" in {
    val s = sucSequent("(\\exists x x>5) <-> (\\exists x x>0)".asFormula)
    val tactic = AxiomaticRuleTactics.equivalenceCongruenceT(PosInExpr(0::Nil))

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>5 <-> x>0".asFormula
  }

  "Exists congruence" should "alpha rename" in {
    val s = sucSequent("(\\exists y y>5) <-> (\\exists y y>0)".asFormula)
    val tactic = AxiomaticRuleTactics.equivalenceCongruenceT(PosInExpr(0::Nil))

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "y>5 <-> y>0".asFormula
  }

  "Imply congruence" should "work" in {
    val s = sucSequent("(x>5 -> x>2) <-> (x>5 -> x>0)".asFormula)
    val tactic = AxiomaticRuleTactics.equivalenceCongruenceT(PosInExpr(1::Nil))

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>2 <-> x>0".asFormula
  }

  "Equiv congruence" should "work" in {
    val s = sucSequent("(x>5 <-> x>2) <-> (x>5 <-> x>0)".asFormula)
    val tactic = AxiomaticRuleTactics.equivalenceCongruenceT(PosInExpr(1::Nil))

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>2 <-> x>0".asFormula
  }

  "And congruence" should "work" in {
    val s = sucSequent("(x>5 & x>2) <-> (x>5 & x>0)".asFormula)
    val tactic = AxiomaticRuleTactics.equivalenceCongruenceT(PosInExpr(1::Nil))

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>2 <-> x>0".asFormula
  }

  "Or congruence" should "work" in {
    val s = sucSequent("(x>5 | x>2) <-> (x>5 | x>0)".asFormula)
    val tactic = AxiomaticRuleTactics.equivalenceCongruenceT(PosInExpr(1::Nil))

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>2 <-> x>0".asFormula
  }

  "Not congruence" should "work" in {
    val s = sucSequent("(!x>2) <-> (!x>0)".asFormula)
    val tactic = AxiomaticRuleTactics.equivalenceCongruenceT(PosInExpr(0::Nil))

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>2 <-> x>0".asFormula
  }

  "CE equivalence congruence" should "prove" in {
    val s = sucSequent("(a=1 & x>0) <-> (a=1 & y>0)".asFormula)
    val tactic = AxiomaticRuleTactics.equivalenceCongruenceT(PosInExpr(1::Nil))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>0 <-> y>0".asFormula
  }

  it should "prove in a universally quantified context" in {
    val s = sucSequent("(\\forall z x>0) <-> (\\forall z y>0)".asFormula)
    val tactic = AxiomaticRuleTactics.equivalenceCongruenceT(PosInExpr(0::Nil))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>0 <-> y>0".asFormula
  }

  it should "prove in a universally quantified context even if quantified name occurs in predicate" in {
    val s = sucSequent("(\\forall x x>0) <-> (\\forall x y>0)".asFormula)
    val tactic = AxiomaticRuleTactics.equivalenceCongruenceT(PosInExpr(0::Nil))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>0 <-> y>0".asFormula
  }

  "CQ equation congruence" should "prove" in {
    val s = sucSequent("a>0 <-> c>0".asFormula)
    val tactic = AxiomaticRuleTactics.equationCongruenceT(PosInExpr(0::Nil))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "a=c".asFormula
  }

  "CO one-sided congruence" should "work" in {
    val s = sequent(Nil, "x=1 & a>0".asFormula :: Nil, "x=1 & c>0".asFormula :: Nil)
    val tactic = AxiomaticRuleTactics.onesidedCongruenceT(PosInExpr(1::Nil))
    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "a>0 <-> c>0".asFormula
  }

  it should "not be applicable when contexts are not equal" in {
    val s = sequent(Nil, "x=1 & a>0".asFormula :: Nil, "x=2 & c>0".asFormula :: Nil)
    val tactic = AxiomaticRuleTactics.onesidedCongruenceT(PosInExpr(1::Nil))
    tactic.applicable(new RootNode(s)) shouldBe false
  }

  it should "not be applicable when antecedent or succedent are not of length 1" in {
    val s = sequent(Nil, "x=1 & a>0".asFormula :: "a=2".asFormula :: Nil, "x=1 & c>0".asFormula :: Nil)
    val t = sequent(Nil, "x=1 & a>0".asFormula :: Nil, "x=1 & c>0".asFormula :: "a=2".asFormula :: Nil)
    val tactic = AxiomaticRuleTactics.onesidedCongruenceT(PosInExpr(1::Nil))
    tactic.applicable(new RootNode(s)) shouldBe false
    tactic.applicable(new RootNode(t)) shouldBe false
  }
}
