import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics._
import testHelper.ProvabilityTestHelper
import org.scalatest.{BeforeAndAfterEach, FlatSpec, Matchers}
import testHelper.SequentFactory._
import testHelper.StringConverter._

import scala.collection.immutable.Map

/**
 * Created by smitsch on 3/16/15.
 * @author Stefan Mitsch
 */
class ContextTacticTests extends FlatSpec with Matchers with BeforeAndAfterEach {
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

  "Cut equivalence in context" should "cut in an equivalence in context if lhs is present" in {
    val s = sucSequent("(x>5 | y<2 & z=3 -> \\forall x. \\exists y. <?y>5;>[x:=1;](x<=1 & x>=1))".asFormula)
    val tactic = ContextTactics.cutInContext("(x<=1 & x>=1) <-> x=1".asFormula, SuccPosition(0, PosInExpr(1::0::0::1::1::Nil)))

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 2

    result.openGoals()(0).sequent.ante should contain only
      "(x>5 | y<2 & z=3 -> \\forall x. \\exists y. <?y>5;>[x:=1;](x<=1 & x>=1)) <-> (x>5 | y<2 & z=3 -> \\forall x. \\exists y. <?y>5;>[x:=1;]x=1)".asFormula
    result.openGoals()(0).sequent.succ should contain only
      "(x>5 | y<2 & z=3 -> \\forall x. \\exists y. <?y>5;>[x:=1;](x<=1 & x>=1))".asFormula

    result.openGoals()(1).sequent.ante shouldBe empty
    result.openGoals()(1).sequent.succ should contain only (
      "(x>5 | y<2 & z=3 -> \\forall x. \\exists y. <?y>5;>[x:=1;](x<=1 & x>=1))".asFormula,
      "(x>5 | y<2 & z=3 -> \\forall x. \\exists y. <?y>5;>[x:=1;](x<=1 & x>=1)) <-> (x>5 | y<2 & z=3 -> \\forall x. \\exists y. <?y>5;>[x:=1;]x=1)".asFormula
      )
  }

  "Cut equivalence in context" should "cut in an equivalence in context if rhs is present" in {
    val s = sucSequent("(x>5 | y<2 & z=3 -> \\forall x. \\exists y. <?y>5;>[x:=1;](x<=1 & x>=1))".asFormula)
    val tactic = ContextTactics.cutInContext("x=1 <-> (x<=1 & x>=1)".asFormula, SuccPosition(0, PosInExpr(1::0::0::1::1::Nil)))

    val result = helper.runTactic(tactic, new RootNode(s))
    result.openGoals() should have size 2

    result.openGoals()(0).sequent.ante should contain only
      "(x>5 | y<2 & z=3 -> \\forall x. \\exists y. <?y>5;>[x:=1;]x=1) <-> (x>5 | y<2 & z=3 -> \\forall x. \\exists y. <?y>5;>[x:=1;](x<=1 & x>=1))".asFormula
    result.openGoals()(0).sequent.succ should contain only
      "(x>5 | y<2 & z=3 -> \\forall x. \\exists y. <?y>5;>[x:=1;](x<=1 & x>=1))".asFormula

    result.openGoals()(1).sequent.ante shouldBe empty
    result.openGoals()(1).sequent.succ should contain only (
      "(x>5 | y<2 & z=3 -> \\forall x. \\exists y. <?y>5;>[x:=1;](x<=1 & x>=1))".asFormula,
      "(x>5 | y<2 & z=3 -> \\forall x. \\exists y. <?y>5;>[x:=1;]x=1) <-> (x>5 | y<2 & z=3 -> \\forall x. \\exists y. <?y>5;>[x:=1;](x<=1 & x>=1))".asFormula
      )
  }
}
