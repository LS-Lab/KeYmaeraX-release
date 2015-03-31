import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.{EqualityRewritingImpl, Interpreter, Tactics}
import edu.cmu.cs.ls.keymaera.tests.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, Matchers, FlatSpec}
import testHelper.SequentFactory._
import testHelper.StringConverter._

import scala.collection.immutable.Map

/**
 * Created by smitsch on 3/16/15.
 * @author Stefan Mitsch
 */
class EqualityRewritingTests extends FlatSpec with Matchers with BeforeAndAfterEach {
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

  "Equality rewriting" should "not apply <-> unsoundly" in {
    val s = sequent(Nil, "x'=0".asFormula :: "(x*y())' <= 0 <-> 0 <= 0".asFormula :: Nil,
      "[x':=1;]0<=0 -> [x':=1;]((x*y()) <= 0)'".asFormula :: Nil)
    val tactic = EqualityRewritingImpl.equalityRewriting(AntePosition(1), SuccPosition(0, PosInExpr(1::1::Nil)))
    tactic.applicable(new RootNode(s)) shouldBe false

    an [IllegalArgumentException] should be thrownBy
      new EqualityRewriting(AntePosition(0), SuccPosition(0, PosInExpr(1::1::Nil))).apply(s)
  }

  it should "not apply = unsoundly" in {
    val s = sequent(Nil, "x'=0".asFormula :: "(x*y())' = 0".asFormula :: Nil,
      "[x':=1;]0<=0 -> [x':=1;](x*y())' <= 0".asFormula :: Nil)
    val tactic = EqualityRewritingImpl.equalityRewriting(AntePosition(1), SuccPosition(0, PosInExpr(1::1::Nil)))
    tactic.applicable(new RootNode(s)) shouldBe false

    an [IllegalArgumentException] should be thrownBy
      new EqualityRewriting(AntePosition(0), SuccPosition(0, PosInExpr(1::1::Nil))).apply(s)
  }

  "Equivalence rewriting" should "rewrite if lhs occurs in succedent" in {
    val s = sequent(Nil, "x>=0 <-> y>=0".asFormula :: Nil, "x>=0".asFormula :: Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(0), SuccPosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "y>=0".asFormula
  }

  it should "rewrite if rhs occurs in succedent" in {
    val s = sequent(Nil, "x>=0 <-> y>=0".asFormula :: Nil, "y>=0".asFormula :: Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(0), SuccPosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) shouldBe empty
    result.openGoals().flatMap(_.sequent.succ) should contain only "x>=0".asFormula
  }

  it should "rewrite if lhs occurs in antecedent" in {
    val s = sequent(Nil, "x>=0 <-> y>=0".asFormula :: "x>=0".asFormula :: Nil, Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(0), AntePosition(1))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "y>=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) shouldBe empty
  }

  it should "rewrite if lhs occurs in antecedent before assumption" in {
    val s = sequent(Nil, "x>=0".asFormula :: "x>=0 <-> y>=0".asFormula :: Nil, Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(1), AntePosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "y>=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) shouldBe empty
  }

  it should "rewrite if rhs occurs in antecedent" in {
    val s = sequent(Nil, "x>=0 <-> y>=0".asFormula :: "y>=0".asFormula :: Nil, Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(0), AntePosition(1))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x>=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) shouldBe empty
  }

  it should "rewrite if rhs occurs in antecedent before assumption" in {
    val s = sequent(Nil, "y>=0".asFormula :: "x>=0 <-> y>=0".asFormula :: Nil, Nil)
    val tactic = EqualityRewritingImpl.equivRewriting(AntePosition(1), AntePosition(0))
    val result = helper.runTactic(tactic, new RootNode(s))

    result.openGoals() should have size 1
    result.openGoals().flatMap(_.sequent.ante) should contain only "x>=0".asFormula
    result.openGoals().flatMap(_.sequent.succ) shouldBe empty
  }
}
