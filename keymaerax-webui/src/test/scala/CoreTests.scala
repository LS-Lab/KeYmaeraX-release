/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import edu.cmu.cs.ls.keymaerax.tags.{CheckinTest, SummaryTest}
import org.scalatest._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr.HereP
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.collection.immutable._
import scala.language.implicitConversions

@CheckinTest
@SummaryTest
class CoreTests extends FlatSpec with Matchers with BeforeAndAfterAll {

  override def beforeAll(): Unit = {
    Configuration.setConfiguration(FileConfiguration)
  }
  
  private val p = PredOf(Function("p", None, Unit, Bool), Nothing)
  private val q = PredOf(Function("q", None, Unit, Bool), Nothing)

  private val sPos = SeqPos(1).asInstanceOf[SuccPos]
  private val aPos = SeqPos(-1).asInstanceOf[AntePos]

  private val x = Variable("x", None, Real)
  private val y = Variable("y", None, Real)
  private val z = Variable("z", None, Real)


  "Core (Data Strutures)" should "accept explicit differential equations" in {
    AtomicODE(DifferentialSymbol(x), Number(5)) should be (AtomicODE(DifferentialSymbol(x), Number(5)))
  }

  it should "require explicit-form differential equation" in {
    an[CoreException] should be thrownBy {AtomicODE(DifferentialSymbol(x), DifferentialSymbol(x))}
  }

  it should "require explicit-form differential equations" in {
    an [CoreException] should be thrownBy {AtomicODE(DifferentialSymbol(x), DifferentialSymbol(x))}
    an [CoreException] should be thrownBy {AtomicODE(DifferentialSymbol(x), DifferentialSymbol(y))}
    an [CoreException] should be thrownBy {AtomicODE(DifferentialSymbol(x), Differential(x))}
    an [CoreException] should be thrownBy {AtomicODE(DifferentialSymbol(x), Differential(y))}
    an [CoreException] should be thrownBy {AtomicODE(DifferentialSymbol(x), Differential(Plus(x, y)))}
    an [CoreException] should be thrownBy {AtomicODE(DifferentialSymbol(x), Plus(x, Differential(Plus(x, y))))}
    an [CoreException] should be thrownBy {AtomicODE(DifferentialSymbol(x), Plus(x, Minus(y, DifferentialSymbol(z))))}
  }

  it should "reject duplicate differential equations" in {
    an [CoreException] should be thrownBy {DifferentialProduct(AtomicODE(DifferentialSymbol(x), Number(7)), AtomicODE(DifferentialSymbol(Variable("x")), Number(2)))}
    an [CoreException] should be thrownBy {DifferentialProduct(AtomicODE(DifferentialSymbol(x), Number(7)), AtomicODE(DifferentialSymbol(Variable("x")), Number(7)))}
  }

  //@todo add core SeqPos tests

  "Tactic (Positions)" should "have HereP == new PosInExpr(Nil)" in {
    HereP should be (new PosInExpr(Nil))
    HereP should be (new PosInExpr(List()))
  }

  "Tactic (Positions)" should "have PosInExpr equality based on lists" in {
    new PosInExpr(List(1,0,4,4,1)) shouldBe new PosInExpr(List(1,0,4,4,1))
    new PosInExpr(List(1,0,4,4,1)) should not be new PosInExpr(List(1,0,4,1))
    new PosInExpr(List(1,0,4,4,1)) should not be new PosInExpr(List(1,0,4,1,4))
    new PosInExpr(List(0)) should not be new PosInExpr(List(0, 0, 0, 0, 0))
    new PosInExpr(List(0)) should not be HereP
  }

  "Core (Expressions)" should "yield equality" in {
    DifferentialFormula(Equal(Variable("x", None, Real), Number(0))) should be (DifferentialFormula(Equal(Variable("x", None, Real), Number(0))))
    Power(Variable("x", None, Real), Number(2)) should be (Power(Variable("x", None, Real), Number(2)))
  }

  def seq(a: Seq[Formula], b: Seq[Formula]): Sequent = Sequent(IndexedSeq() ++ a, IndexedSeq() ++ b)

  def testRule(rule: Rule, in: Sequent, out: List[Sequent]): Unit = {
    println("\tCheck " + rule) //@TODO turn into "should" output?
    val pn = ProvableSig.startPlainProof(in)
    val resList = pn.apply(rule, 0).subgoals
    println("\tResult\t" + resList)
    println("\tExpected\t" + out)
    if (resList != out) println("Unexpected")
    resList.length should be (out.length)
    val res = resList
    for((s,t) <- res zip out) {
      s.ante.length should be (t.ante.length)
      for((f,g) <- s.ante zip t.ante)
        f should be (g)
      
      s.succ.length should be (t.succ.length)
      for((f,g) <- s.succ zip t.succ)
        f should be (g)
    }
  }

  private def testRule(rule: Rule, in: Sequent) = ProvableSig.startPlainProof(in).apply(rule, 0).subgoals

  private implicit def form2SeqForm(f: Formula): Seq[Formula] = Seq(f)

  private implicit def sequentToList(s: Sequent): List[Sequent] = List(s)

  "Core (Propositional Rules)" should "yield expected results" in {
    testRule(CloseTrue(sPos), seq(Nil, True), Nil)
    testRule(CloseFalse(aPos), seq(False, Nil), Nil)

    testRule(NotRight(sPos), seq(Nil, Not(p)), seq(p, Nil))
    testRule(NotLeft(aPos), seq(Not(p), Nil), seq(Nil, p))
    testRule(ImplyRight(sPos), seq(Nil, Imply(p, q)), seq(p, q))
    testRule(ImplyLeft(aPos), seq(Imply(p, q), Nil), seq(Nil, p) ++ seq(q, Nil))
    testRule(AndRight(sPos), seq(Nil, And(p, q)), seq(Nil, p) ++ seq(Nil, q))
    testRule(AndLeft(aPos), seq(And(p, q), Nil), seq(p ++ q, Nil))
    testRule(OrRight(sPos), seq(Nil, Or(p, q)), seq(Nil, p ++ q))
    testRule(OrLeft(aPos), seq(Or(p, q), Nil), seq(p, Nil) ++ seq(q, Nil))
    //@TODO The following two tests fail since Equivs have been currently changed to a single formula
    testRule(EquivRight(sPos), seq(Nil, Equiv(p, q)), seq(p, q) ++ seq(q, p))
    testRule(EquivLeft(aPos), seq(Equiv(p, q), Nil), seq(And(p, q), Nil) ++ seq(And(Not(p), Not(q)), Nil))
  }

  it should "complain about being applied to formulas of the wrong shape" in {
    var sPos = SeqPos(1).asInstanceOf[SuccPos]
    var aPos = SeqPos(-1).asInstanceOf[AntePos]
    val s = Sequent(IndexedSeq(And(p, Not(p)), Imply(p, q), q), IndexedSeq(And(Not(Equiv(p,Not(p))), q), Not(q), p))

    an [MatchError] should be thrownBy testRule(NotRight(sPos), s)
    an [MatchError] should be thrownBy testRule(NotLeft(aPos), s)
    an [MatchError] should be thrownBy testRule(OrRight(sPos), s)
    an [MatchError] should be thrownBy testRule(OrLeft(aPos), s)
    // an [MatchError] should be thrownBy testRule(AndRight(sPos), s)
    // an [MatchError] should be thrownBy testRule(AndLeft(aPos), s)
    an [MatchError] should be thrownBy testRule(ImplyRight(sPos), s)
    an [MatchError] should be thrownBy testRule(ImplyLeft(aPos), s)
    an [MatchError] should be thrownBy testRule(EquivRight(sPos), s)
    an [MatchError] should be thrownBy testRule(EquivLeft(aPos), s)
    an [InapplicableRuleException] should be thrownBy testRule(CloseTrue(sPos), s)
    an [InapplicableRuleException] should be thrownBy testRule(CloseFalse(aPos), s)

    sPos = SeqPos(2).asInstanceOf[SuccPos]
    aPos = SeqPos(-2).asInstanceOf[AntePos]
    //an [MatchError] should be thrownBy testRule(NotRight(sPos), s)
    an [MatchError] should be thrownBy testRule(NotLeft(aPos), s)
    an [MatchError] should be thrownBy testRule(OrRight(sPos), s)
    an [MatchError] should be thrownBy testRule(OrLeft(aPos), s)
    an [MatchError] should be thrownBy testRule(AndRight(sPos), s)
    an [MatchError] should be thrownBy testRule(AndLeft(aPos), s)
    an [MatchError] should be thrownBy testRule(ImplyRight(sPos), s)
    //an [MatchError] should be thrownBy testRule(ImplyLeft(aPos), s)
    an [MatchError] should be thrownBy testRule(EquivRight(sPos), s)
    an [MatchError] should be thrownBy testRule(EquivLeft(aPos), s)
    an [InapplicableRuleException] should be thrownBy testRule(CloseTrue(sPos), s)
    an [InapplicableRuleException] should be thrownBy testRule(CloseFalse(aPos), s)

    sPos = SeqPos(3).asInstanceOf[SuccPos]
    aPos = SeqPos(-3).asInstanceOf[AntePos]
    an [MatchError] should be thrownBy testRule(NotRight(sPos), s)
    an [MatchError] should be thrownBy testRule(NotLeft(aPos), s)
    an [MatchError] should be thrownBy testRule(OrRight(sPos), s)
    an [MatchError] should be thrownBy testRule(OrLeft(aPos), s)
    an [MatchError] should be thrownBy testRule(AndRight(sPos), s)
    an [MatchError] should be thrownBy testRule(AndLeft(aPos), s)
    an [MatchError] should be thrownBy testRule(ImplyRight(sPos), s)
    an [MatchError] should be thrownBy testRule(ImplyLeft(aPos), s)
    an [MatchError] should be thrownBy testRule(EquivRight(sPos), s)
    an [MatchError] should be thrownBy testRule(EquivLeft(aPos), s)
    an [InapplicableRuleException] should be thrownBy testRule(CloseTrue(sPos), s)
    an [InapplicableRuleException] should be thrownBy testRule(CloseFalse(aPos), s)
  }

  it should "complain about being applied to non-existent positions" in {
    val s = Sequent(IndexedSeq(And(p, Not(p)), Imply(p, q), q), IndexedSeq(And(Not(Equiv(p,Not(p))), q), Not(q), p))

    val sPos = SeqPos(5).asInstanceOf[SuccPos]
    val aPos = SeqPos(-5).asInstanceOf[AntePos]
    an [IndexOutOfBoundsException] should be thrownBy testRule(NotRight(sPos), s)
    an [IndexOutOfBoundsException] should be thrownBy testRule(NotLeft(aPos), s)
    an [IndexOutOfBoundsException] should be thrownBy testRule(OrRight(sPos), s)
    an [IndexOutOfBoundsException] should be thrownBy testRule(OrLeft(aPos), s)
    an [IndexOutOfBoundsException] should be thrownBy testRule(AndRight(sPos), s)
    an [IndexOutOfBoundsException] should be thrownBy testRule(AndLeft(aPos), s)
    an [IndexOutOfBoundsException] should be thrownBy testRule(ImplyRight(sPos), s)
    an [IndexOutOfBoundsException] should be thrownBy testRule(ImplyLeft(aPos), s)
    an [IndexOutOfBoundsException] should be thrownBy testRule(EquivRight(sPos), s)
    an [IndexOutOfBoundsException] should be thrownBy testRule(EquivLeft(aPos), s)
    an [IndexOutOfBoundsException] should be thrownBy testRule(CloseTrue(sPos), s)
    an [IndexOutOfBoundsException] should be thrownBy testRule(CloseFalse(aPos), s)
  }

  "ensures" should "either throw an exception or not evaluate condition and message" in {
    var cnd1 = false
    var msg1 = false
    var cnd2 = false
    var cnd3 = false
    var msg3 = false
    var cnd4 = false

    def fun1(): Int = { 0 } ensures (r => { cnd1 = true; r > 0 }, { msg1 = true; "non-positive" })

    def fun2(): Int = { 0 } ensures (r => { cnd2 = true; r > 0 })

    def fun3(): Int = { 0 } ensures ({ cnd3 = true; false }, { msg3 = true; "false" })

    def fun4(): Int = { 0 } ensures { cnd4 = true; false }

    // check if assertions are enabled
    try {
      assertion(false)
      // no exception was thrown:
      // assertions are disabled (java -da) or elided (scalacOptions ++= Seq("-Xdisable-assertions"))
      println("Assertions Disabled")
      // no side effects should occur
      fun1() shouldBe 0
      cnd1 shouldBe false
      msg1 shouldBe false

      fun2() shouldBe 0
      cnd2 shouldBe false

      fun3() shouldBe 0
      cnd3 shouldBe false
      msg3 shouldBe false

      fun4() shouldBe 0
      cnd4 shouldBe false
    }
    catch {
      // assertions are enabled (java -ea)
      case e: AssertionError =>
        println("Assertions Enabled")
        e.getMessage shouldBe "assertion failed"
        // exceptions
        the[AssertionError] thrownBy fun1() should have message "assertion failed: non-positive"
        the[AssertionError] thrownBy fun2() should have message "assertion failed"
        the[AssertionError] thrownBy fun3() should have message "assertion failed: false"
        the[AssertionError] thrownBy fun4() should have message "assertion failed"
        // side effects
        cnd1 shouldBe true
        cnd2 shouldBe true
        cnd3 shouldBe true
        cnd4 shouldBe true
        msg1 shouldBe true
        msg3 shouldBe true
    }
  }
}
