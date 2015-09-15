/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/

import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, CheckinTest}
import org.scalatest._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics._
import edu.cmu.cs.ls.keymaerax.tools._
import java.math.BigDecimal
import java.io.File
import scala.collection.immutable._

@CheckinTest
@SummaryTest
class CoreTests extends FlatSpec with Matchers {
  
  val p = PredOf(Function("p", None, Unit, Bool), Nothing)
  val q = PredOf(Function("q", None, Unit, Bool), Nothing)

  val sPos = SuccPosition(0)
  val aPos = AntePosition(0)

  val x = Variable("x", None, Real)
  val y = Variable("y", None, Real)
  val z = Variable("z", None, Real)


  "Core (Data Strutures)" should "accept explicit differential equations" in {
    new AtomicODE(new DifferentialSymbol(x), new Number(5)) should be (new AtomicODE(new DifferentialSymbol(x), new Number(5)))
  }

  it should "require explicit-form differential equation" in {
    an[CoreException] should be thrownBy {new AtomicODE(new DifferentialSymbol(x), new DifferentialSymbol(x))}
  }

  it should "require explicit-form differential equations" in {
    an [CoreException] should be thrownBy {new AtomicODE(new DifferentialSymbol(x), new DifferentialSymbol(x))}
    an [CoreException] should be thrownBy {new AtomicODE(new DifferentialSymbol(x), new DifferentialSymbol(y))}
    an [CoreException] should be thrownBy {new AtomicODE(new DifferentialSymbol(x), new Differential(x))}
    an [CoreException] should be thrownBy {new AtomicODE(new DifferentialSymbol(x), new Differential(y))}
    an [CoreException] should be thrownBy {new AtomicODE(new DifferentialSymbol(x), new Differential(Plus(x, y)))}
    an [CoreException] should be thrownBy {new AtomicODE(new DifferentialSymbol(x), Plus(x, new Differential(Plus(x, y))))}
    an [CoreException] should be thrownBy {new AtomicODE(new DifferentialSymbol(x), Plus(x, Minus(y, DifferentialSymbol(z))))}
  }

  it should "reject duplicate differential equations" in {
    an [CoreException] should be thrownBy {DifferentialProduct(new AtomicODE(new DifferentialSymbol(x), Number(7)), new AtomicODE(new DifferentialSymbol(new Variable("x")), Number(2)))}
    an [CoreException] should be thrownBy {DifferentialProduct(new AtomicODE(new DifferentialSymbol(x), Number(7)), new AtomicODE(new DifferentialSymbol(new Variable("x")), Number(7)))}
  }

  //@todo add core SeqPos tests

  "Tactic (Positions)" should "have HereP == new PosInExpr(Nil)" in {
    HereP should be (new PosInExpr(Nil))
    HereP should be (new PosInExpr(List()))
  }

  "Tactic (Positions)" should "have PosInExpr equality based on lists" in {
    new PosInExpr(List(1,0,4,4,1)) should be (new PosInExpr(List(1,0,4,4,1)))
    new PosInExpr(List(1,0,4,4,1)) should not be (new PosInExpr(List(1,0,4,1)))
    new PosInExpr(List(1,0,4,4,1)) should not be (new PosInExpr(List(1,0,4,1,4)))
    new PosInExpr(List(0)) should not be (new PosInExpr(List(0, 0, 0, 0, 0)))
    new PosInExpr(List(0)) should not be (HereP)
  }

  "Core (Expressions)" should "yield equality" in {
    DifferentialFormula(Equal(Variable("x", None, Real), Number(0))) should be (DifferentialFormula(Equal(Variable("x", None, Real), Number(0))))
    Power(Variable("x", None, Real), Number(2)) should be (Power(Variable("x", None, Real), Number(2)))
  }

  def rootSucc(f: Formula) = new RootNode(Sequent(Nil, IndexedSeq(), IndexedSeq(f)))
  def rootAnte(f: Formula) = new RootNode(Sequent(Nil, IndexedSeq(f), IndexedSeq()))

  def seq(a: Seq[Formula], b: Seq[Formula]): Sequent = Sequent(Nil, IndexedSeq() ++ a, IndexedSeq() ++ b)

  def testRule(rule: Rule, in: Sequent, out: List[Sequent]) {
    println("\tCheck " + rule) //@TODO turn into "should" output?
    val pn = new RootNode(in)
    val resList = pn.apply(rule).subgoals
    println("\tResult\t" + resList.map(_.sequent))
    println("\tExpected\t" + out)
    if (resList.map(_.sequent) != out) println("Unexpected")
    resList.length should be (out.length)
    val res = resList.map(_.sequent)
    for((s,t) <- res zip out) {
      s.ante.length should be (t.ante.length)
      for((f,g) <- s.ante zip t.ante)
        f should be (g)
      
      s.succ.length should be (t.succ.length)
      for((f,g) <- s.succ zip t.succ)
        f should be (g)
    }
  }

  def testRule(rule: Rule, in: Sequent) {
    val pn = new RootNode(in)
    val resList = pn.apply(rule).subgoals
    resList.map(_.sequent)
  }

  implicit def form2SeqForm(f: Formula): Seq[Formula] = Seq(f)

  implicit def sequentToList(s: Sequent): List[Sequent] = List(s)

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
  
  it should "complain about being applied to the wrong sequent side" in {
    //@todo adapt to SeqPos
    val sPos = SuccPosition(0)
    val aPos = AntePosition(0)
    val s = Sequent(Nil, IndexedSeq(And(p, Not(p)), Imply(p, q)), IndexedSeq(And(Not(Equiv(p,Not(p))), q), Not(q)))
    an [ClassCastException] should be thrownBy testRule(NotRight(aPos), s)
    an [ClassCastException] should be thrownBy testRule(NotLeft(sPos), s)
    an [ClassCastException] should be thrownBy testRule(AndRight(aPos), s)
    an [ClassCastException] should be thrownBy testRule(AndLeft(sPos), s)
    an [ClassCastException] should be thrownBy testRule(OrRight(aPos), s)
    an [ClassCastException] should be thrownBy testRule(OrLeft(sPos), s)
    an [ClassCastException] should be thrownBy testRule(ImplyRight(aPos), s)
    an [ClassCastException] should be thrownBy testRule(ImplyLeft(sPos), s)
    an [ClassCastException] should be thrownBy testRule(EquivRight(aPos), s)
    an [ClassCastException] should be thrownBy testRule(EquivLeft(sPos), s)
    an [ClassCastException] should be thrownBy testRule(CloseTrue(aPos), s)
    an [ClassCastException] should be thrownBy testRule(CloseFalse(sPos), s)
  }

  // TODO re-introduce assertion into Proof.scala
  ignore should "complain about being applied to non-top-level positions" in {
    val s = Sequent(Nil, IndexedSeq(And(p, Not(p)), Imply(p, q)), IndexedSeq(And(Not(Equiv(p,Not(p))), q), Not(q)))
    val aDeep = AntePosition(0, PosInExpr(List(0,1)))
    aDeep.isIndexDefined(s) should be (true)
    an [IllegalArgumentException] should be thrownBy testRule(NotLeft(aDeep), s)
    an [IllegalArgumentException] should be thrownBy testRule(AndLeft(aDeep), s)
    an [IllegalArgumentException] should be thrownBy testRule(OrLeft(aDeep), s)
    an [IllegalArgumentException] should be thrownBy testRule(ImplyLeft(aDeep), s)
    an [IllegalArgumentException] should be thrownBy testRule(EquivLeft(aDeep), s)
    an [IllegalArgumentException] should be thrownBy testRule(CloseFalse(aDeep), s)

    val sDeep = SuccPosition(0, PosInExpr(List(0,1)))
    sDeep.isIndexDefined(s) should be (true)
    an [IllegalArgumentException] should be thrownBy testRule(NotRight(sDeep), s)
    an [IllegalArgumentException] should be thrownBy testRule(AndRight(sDeep), s)
    an [IllegalArgumentException] should be thrownBy testRule(OrRight(sDeep), s)
    an [IllegalArgumentException] should be thrownBy testRule(ImplyRight(sDeep), s)
    an [IllegalArgumentException] should be thrownBy testRule(EquivRight(sDeep), s)
    an [IllegalArgumentException] should be thrownBy testRule(CloseTrue(sDeep), s)
  }
  
  it should "complain about being applied to formulas of the wrong shape" in {
    var sPos = SuccPosition(0)
    var aPos = AntePosition(0)
    val s = Sequent(Nil, IndexedSeq(And(p, Not(p)), Imply(p, q), q), IndexedSeq(And(Not(Equiv(p,Not(p))), q), Not(q), p))

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

    sPos = SuccPosition(1)
    aPos = AntePosition(1)
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

    sPos = SuccPosition(2)
    aPos = AntePosition(2)
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
    val s = Sequent(Nil, IndexedSeq(And(p, Not(p)), Imply(p, q), q), IndexedSeq(And(Not(Equiv(p,Not(p))), q), Not(q), p))

    var sPos = SuccPosition(4)
    var aPos = AntePosition(4)
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
}
