package LODESolverTests

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper
import edu.cmu.cs.ls.keymaerax.tactics._

import scala.collection.immutable.IndexedSeq

/**
 * Tests term rewriting tactics that were written during the creation of the Logical ODE Solver.
 * These tactics are of more general use whenever preforming term-level rewriting.
 * Created by nfulton on 9/11/15.
 */
class TermRewritingTests extends testHelper.TacticTestSuite {
  "replaceSubterm" should "replace a subterm" in {
    val f = "[{x' = 0*x+1 & 1=1}]2=2".asFormula
    val posInExpr = PosInExpr(0 :: 0 :: 1 :: Nil) // select box, select diff eq, select rhs of equality.
    //make sure we got the position right.
    TacticHelper.getTerm(f, posInExpr).get shouldBe "0*x+1".asTerm
    TermRewriting.replaceSubterm(f, posInExpr, _ => Number(1)).get shouldBe "[{x' = 1 & 1=1}]2=2".asFormula
  }

  it should "work on a more interesting term" in {
    val f = "[{x' = 0*x+1+0*y+0*z & 1=1&3=3}]2=2".asFormula
    val posInExpr = PosInExpr(0 :: 0 :: 1 :: Nil) // select box, select diff eq, select rhs of equality.
    //make sure we got the position right.
    TacticHelper.getTerm(f, posInExpr).get shouldBe "0*x+1+0*y+0*z".asTerm
    TermRewriting.replaceSubterm(f, posInExpr, _ => Number(1)).get shouldBe "[{x' = 1 & 1=1&3=3}]2=2".asFormula
  }

  "Sequent calculus Tern Rewriting" should "work" in {
    val f = "[{x' = 0*x+1 & 1=1}]2=2".asFormula
    val node = helper.formulaToNode(f)

    val posInExpr = PosInExpr(0 :: 0 :: 1 :: Nil) // select box, select diff eq, select rhs of equality.
    val pos = SuccPosition(0, posInExpr)
    val tactic = ODETactics.rewriteConstantTime(pos)

    helper.runTactic(tactic, node)
    fail("no asssertion.")
  }

  "HilbertCalculus.CE" should "work with custom setup code" in {
    val f = "[{x' = 0*x+1 & 1=1}]2=2".asFormula
    val node = helper.formulaToNode(f)

    val provable = Provable.startProof(new Sequent(Nil, IndexedSeq(), IndexedSeq("0*x+1=1".asFormula)))
    val tactic   = HilbertCalculus.CE(provable)(SuccPosition(0, PosInExpr(0 :: 0 :: 1 :: Nil)))

    helper.runTactic(tactic, node)
    fail("No assertions")
  }

  it should "work with TermRewriting setup code" in {
    val f = "[{x' = 0*x+1 & 1=1}]2=2".asFormula
    val node = helper.formulaToNode(f)

    val provable = Provable.startProof(new Sequent(Nil, IndexedSeq(), IndexedSeq("0*x+1=1".asFormula)))
    val tactic   = TermRewriting.hilbertTermRewrite(
      (t:Term) => t match {case Plus(Times(n:Number, x), m) => n.value.toInt==0 case _ => false},
      (t:Term) => t match {case Plus(Times(n, x), m) => m case _ => ???},
      "Prove that 0*x+m = m"
    )(SuccPosition(0, PosInExpr(0 :: 0 :: 1 :: Nil)))

    helper.runTactic(tactic, node)
    fail("No assertions")
  }
}
