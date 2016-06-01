/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

import edu.cmu.cs.ls.keymaerax.tags.{SummaryTest, CheckinTest}
import org.scalatest._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.{AntePosition, PosInExpr, SuccPosition}
import edu.cmu.cs.ls.keymaerax.bellerophon.PosInExpr.HereP
import edu.cmu.cs.ls.keymaerax.tools._
import java.math.BigDecimal
import java.io.File
import scala.collection.immutable._

@CheckinTest
@SummaryTest
class CoreTests extends FlatSpec with Matchers {
  
  val p = PredOf(Function("p", None, Unit, Bool), Nothing)
  val q = PredOf(Function("q", None, Unit, Bool), Nothing)

  val sPos = SeqPos(1).asInstanceOf[SuccPos]
  val aPos = SeqPos(-1).asInstanceOf[AntePos]

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

  def rootSucc(f: Formula) = Provable.startProof(Sequent(IndexedSeq(), IndexedSeq(f)))
  def rootAnte(f: Formula) = Provable.startProof(Sequent(IndexedSeq(f), IndexedSeq()))

  def seq(a: Seq[Formula], b: Seq[Formula]): Sequent = Sequent(IndexedSeq() ++ a, IndexedSeq() ++ b)

  def testRule(rule: Rule, in: Sequent, out: List[Sequent]) {
    println("\tCheck " + rule) //@TODO turn into "should" output?
    val pn = Provable.startProof(in)
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

  def testRule(rule: Rule, in: Sequent) = Provable.startProof(in).apply(rule, 0).subgoals

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
}
