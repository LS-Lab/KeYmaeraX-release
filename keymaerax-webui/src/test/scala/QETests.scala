/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
import edu.cmu.cs.ls.keymaerax.tactics.{Interpreter, RootNode, Tactics}
import edu.cmu.cs.ls.keymaerax.tactics.TactixLibrary._
import testHelper.ProvabilityTestHelper
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import org.scalatest._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools._
import java.math.BigDecimal
import scala.collection.immutable._

/**
 * @author Ran Ji
 */
class QETests extends FlatSpec with Matchers with BeforeAndAfterEach {
  val helper = new ProvabilityTestHelper((x) => println(x))
  val mathematicaConfig: Map[String, String] = helper.mathematicaConfig
  var qet : QETool = null
  val x = Variable("x", None, Real)

  val zero = Number(new BigDecimal("0"))

  def num(n : Integer) = Number(new BigDecimal(n.toString()))
  def snum(n : String) = Number(new BigDecimal(n))

  override def beforeEach() = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
    Tactics.MathematicaScheduler.init(mathematicaConfig)
    Tactics.KeYmaeraScheduler.init(Map())
    qet = new JLinkMathematicaLink()
    qet match {
      case qetml : JLinkMathematicaLink => qetml.init(mathematicaConfig("linkName"), None) //@todo jlink
    }
  }

  override def afterEach() = {
    if (Tactics.MathematicaScheduler != null) Tactics.MathematicaScheduler.shutdown()
    if (Tactics.KeYmaeraScheduler != null) Tactics.KeYmaeraScheduler.shutdown()
    Tactics.MathematicaScheduler = null
    Tactics.KeYmaeraScheduler = null
    qet match {
      case qetml : JLinkMathematicaLink => qetml.shutdown()
    }
    qet = null
  }

  "Quantifier Eliminator" should "verify that there exists x > 0" in {
    val f = Exists(Seq(x), Greater(x, zero))
    qet.qe(f) should be (True)
  }

  it should "prove" in {
    qet.qe("(x+y-z)^3 = 1 -> true".asFormula) should be("true".asFormula)
  }

  it should "be provable" in {
    val s = Sequent(Nil, IndexedSeq(), IndexedSeq("(x+y-z)^3 = 1 -> true".asFormula))
    val tactic = QE
    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  it should "not prove" in {
    qet.qe("\\forall x_0 (x_0>1->x_0>2)".asFormula) should be("false".asFormula)
  }

  it should "not be provable with counter example" in {
    val s = Sequent(Nil, IndexedSeq(), IndexedSeq("x_0>1->x_0<1".asFormula))
    val tactic = CntEx
    helper.runTactic(tactic, new RootNode(s)).openGoals().head.sequent shouldBe s
  }

  it should "not be provable with counter example forall" in {
    val s = Sequent(Nil, IndexedSeq(), IndexedSeq("\\forall x_0 (x_0>1->x_0<1)".asFormula))
    val tactic = CntEx
    helper.runTactic(tactic, new RootNode(s)).openGoals().head.sequent shouldBe s
  }

  it should "be provable with no counter example exists" in {
    val s = Sequent(Nil, IndexedSeq(), IndexedSeq("\\exists x_0 (x_0>1->x_0<1)".asFormula))
    val tactic = CntEx | QE
    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  it should "not be provable with counter example double" in {
    val s = Sequent(Nil, IndexedSeq(), IndexedSeq("x_0>y_0->x_0<y_0".asFormula))
    val tactic = CntEx
    helper.runTactic(tactic, new RootNode(s)).openGoals().head.sequent shouldBe s
  }

  it should "not be provable with counter example forall forall" in {
    val s = Sequent(Nil, IndexedSeq(), IndexedSeq("\\forall x_0 \\forall y_0 (x_0>y_0->x_0<y_0)".asFormula))
    val tactic = CntEx
    helper.runTactic(tactic, new RootNode(s)).openGoals().head.sequent shouldBe s
  }

  it should "be provable with no counter example forall exists" in {
    val s = Sequent(Nil, IndexedSeq(), IndexedSeq("\\forall x_0 \\exists y_0 (x_0>y_0->x_0<y_0)".asFormula))
    val tactic = CntEx | QE
    helper.runTactic(tactic, new RootNode(s)) shouldBe 'closed
  }

  it should "not be provable with counter exists forall" in {
    val s = Sequent(Nil, IndexedSeq(), IndexedSeq("\\exists y_0 \\forall x_0 (x_0>y_0->x_0<y_0)".asFormula))
    val tactic = CntEx
    helper.runTactic(tactic, new RootNode(s)).openGoals().head.sequent shouldBe s
  }
}