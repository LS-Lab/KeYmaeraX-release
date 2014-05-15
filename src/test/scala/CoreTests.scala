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
  }

  def rootSucc(f: Formula) = new RootNode(Sequent(Nil, IndexedSeq(), IndexedSeq(f)))
  def rootAnte(f: Formula) = new RootNode(Sequent(Nil, IndexedSeq(f), IndexedSeq()))

  def testImplyRight = {
    val pn = rootSucc(Imply(p, q))
    val res = pn.apply(ImplyRight(sPos))
    res.length should be (1)
    val ante = res.head.sequent.ante 
    val succ = res.head.sequent.succ 
    ante.length should be (1)
    succ.length should be (1)
    ante(0) should be (p)
    succ(0) should be (q)
  }

  def testImplyLeft = {
    val pn = rootAnte(Imply(p, q))
    val res = pn.apply(ImplyLeft(aPos))
    res.length should be (2)
    val ante = res(_:Int).sequent.ante 
    val succ = res(_:Int).sequent.succ 
    ante(0).length should be (0)
    succ(0).length should be (1)
    succ(0)(0) should be (p)
    ante(1).length should be (1)
    succ(1).length should be (0)
    ante(1)(0) should be (q)
  }

  "Core (Propositional Rules)" should "yield expected results" in {
    testImplyRight
    testImplyLeft
  }
}
