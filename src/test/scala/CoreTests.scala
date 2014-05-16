import org.scalatest._
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tools._
import java.math.BigDecimal
import java.io.File

class CoreTests extends FlatSpec with Matchers {
  
  val p = PredicateConstant("p", None)
  val q = PredicateConstant("q", None)

  val sPos = SuccPosition(0)
  val aPos = AntePosition(0)

  "Core (Positions)" should "have HereP == new PosInExpr(Nil)" in {
    HereP should be (new PosInExpr(Nil))
  }

  "Core (Positions)" should "have PosInExpr equality based on lists" in {
    new PosInExpr(List(1,0,4,4,1)) should be (new PosInExpr(List(1,0,4,4,1)))
    new PosInExpr(List(1,0,4,4,1)) should not be (new PosInExpr(List(1,0,4,1)))
    new PosInExpr(List(1,0,4,4,1)) should not be (new PosInExpr(List(1,0,4,1,4)))
    new PosInExpr(List(0)) should not be (new PosInExpr(List(0, 0, 0, 0, 0)))
  }

  def rootSucc(f: Formula) = new RootNode(Sequent(Nil, IndexedSeq(), IndexedSeq(f)))
  def rootAnte(f: Formula) = new RootNode(Sequent(Nil, IndexedSeq(f), IndexedSeq()))

  def seq(a: Seq[Formula], b: Seq[Formula]): Sequent = Sequent(Nil, IndexedSeq() ++ a, IndexedSeq() ++ b)

  def testRule(rule: Rule, in: Sequent, out: List[Sequent]) {
    val pn = new RootNode(in)
    val resList = pn.apply(rule)
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

  implicit def form2SeqForm(f: Formula): Seq[Formula] = Seq(f)

  implicit def sequentToList(s: Sequent): List[Sequent] = List(s)

  "Core (Propositional Rules)" should "yield expected results" in {
    testRule(NotRight(sPos), seq(Nil, Not(p)), seq(p, Nil))
    testRule(NotLeft(aPos), seq(Not(p), Nil), seq(Nil, p))
    testRule(ImplyRight(sPos), seq(Nil, Imply(p, q)), seq(p, q))
    testRule(ImplyLeft(aPos), seq(Imply(p, q), Nil), seq(Nil, p) ++ seq(q, Nil))
    testRule(AndRight(sPos), seq(Nil, And(p, q)), seq(Nil, p) ++ seq(Nil, q))
    testRule(AndLeft(aPos), seq(And(p, q), Nil), seq(p ++ q, Nil))
    testRule(OrRight(sPos), seq(Nil, Or(p, q)), seq(Nil, p ++ q))
    testRule(OrLeft(aPos), seq(Or(p, q), Nil), seq(p, Nil) ++ seq(q, Nil))
    testRule(EquivRight(sPos), seq(Nil, Equiv(p, q)), seq(p, q) ++ seq(q, p))
    testRule(EquivLeft(aPos), seq(Equiv(p, q), Nil), seq(And(p, q), Nil) ++ seq(And(Not(p), Not(q)), Nil))
  }
}
