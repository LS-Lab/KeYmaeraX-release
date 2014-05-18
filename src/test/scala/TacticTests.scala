import edu.cmu.cs.ls.keymaera.tactics.Tactics.Tactic
import org.scalatest._
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tools._
import java.math.BigDecimal
import java.io.File

import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._

class TacticTests extends FlatSpec with Matchers {
  Config.mathlicenses = 1
  Config.maxCPUs = 1
  val math = new Mathematica
  val qet = new JLinkMathematicaLink()
  val x = Variable("x", None, Real)
  val y = Variable("y", None, Real)

  val zero = Number(new BigDecimal("0"))

  val one = Number(new BigDecimal("1"))

  val xgeq0 = GreaterEquals(Real, x, zero)
  val xgt0 = GreaterThan(Real, x, zero)
  val xplus1 = Add(Real, x, one)
  val xplus1gtx = GreaterThan(Real, xplus1, x)

  def num(n : Integer) = Number(new BigDecimal(n.toString()))
  def snum(n : String) = Number(new BigDecimal(n))

  "Tactics" should "learn a lemma from (x > 0 & y > x) -> x >= 0" in {
    val f = TacticLibrary.universalClosure(Imply(And(xgt0, GreaterThan(Real, y, x)), xgeq0))
    qet.qe(f) should be (True)
    LookupLemma.addRealArithLemma(math, f) match {
      case Some((file, id, res)) => 
        (res match {
          case Equiv(_, True) => true
          case _ => false
        }) should be (true)
        val r = new RootNode(new Sequent(Nil, Vector(), Vector()))
        val t = LookupLemma(file,id)
        val nr = r.apply(t).head
        nr.sequent.ante(nr.sequent.ante.length-1) should be (res)
      case None => "Lemma creation" should be ("successful")
    }
  }

  "Tactics" should "learn a lemma from (x > 0 & y = x+1 & y > x) -> (x >= 0 & y > 0)" in {
    val f = TacticLibrary.universalClosure(Imply(And(And(xgt0, Equals(Real, y, xplus1)), GreaterThan(Real, y, x)), And(xgeq0, GreaterThan(Real, y, zero))))
    qet.qe(f) should be (True)
    LookupLemma.addRealArithLemma(math, f) match {
      case Some((file, id, res)) => 
        (res match {
          case Equiv(_, True) => true
          case _ => false
        }) should be (true)
        val r = new RootNode(new Sequent(Nil, Vector(), Vector()))
        val t = LookupLemma(file,id)
        val nr = r.apply(t).head
        nr.sequent.ante(nr.sequent.ante.length-1) should be (res)
      case None => "Lemma creation" should be ("successful")
    }
  }

  "Tactics" should "learn a lemma from (x > 0 & y = x+1 & y > x) -> (y > 0)" in {
    val f = TacticLibrary.universalClosure(Imply(And(And(xgt0, Equals(Real, y, xplus1)), GreaterThan(Real, y, x)), GreaterThan(Real, y, zero)))
    qet.qe(f) should be (True)
    LookupLemma.addRealArithLemma(math, f) match {
      case Some((file, id, res)) => 
        (res match {
          case Equiv(_, True) => true
          case _ => false
        }) should be (true)
        val r = new RootNode(new Sequent(Nil, Vector(), Vector()))
        val t = LookupLemma(file,id)
        val nr = r.apply(t).head
        nr.sequent.ante(nr.sequent.ante.length-1) should be (res)
      case None => "Lemma creation" should be ("successful")
    }
  }

  "Tactics" should "learn a lemma from (x > 0 & y = x+1 & x+1 > x) -> (x+1 > 0)" in {
    val f = TacticLibrary.universalClosure(Imply(And(And(xgt0, Equals(Real, y, xplus1)), GreaterThan(Real, xplus1, x)), GreaterThan(Real, xplus1, zero)))
    qet.qe(f) should be (True)
    LookupLemma.addRealArithLemma(math, f) match {
      case Some((file, id, res)) => 
        (res match {
          case Equiv(_, True) => true
          case _ => false
        }) should be (true)
        val r = new RootNode(new Sequent(Nil, Vector(), Vector()))
        val t = LookupLemma(file,id)
        val nr = r.apply(t).head
        nr.sequent.ante(nr.sequent.ante.length-1) should be (res)
      case None => "Lemma creation" should be ("successful")
    }
  }

  def tryTactic(tactic: Tactic): ProofNode = {
    val x = Variable("x", None, Real)
    val y = Variable("y", None, Real)
    val xp1 = Add(Real, x, Number(1))
    val zero = Number(0)
    val r = new RootNode(new Sequent(Nil, Vector(GreaterThan(Real, x, zero), Equals(Real, y, xp1), Imply(And(GreaterThan(Real, x, zero), Equals(Real, y, xp1)), GreaterThan(Real, xp1, zero))), Vector(GreaterThan(Real, xp1, zero))))
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
    while(!(Tactics.KeYmaeraScheduler.blocked == Tactics.KeYmaeraScheduler.maxThreads && Tactics.KeYmaeraScheduler.prioList.isEmpty)) {
      Thread.sleep(10)
    }
    r
  }

  def checkSingleAlternative(p: ProofNode): Boolean =
    if(p.children.length > 1) {
      println("found two alternatives " + p.children)
      false
    } else if(p.children.length > 0)
      p.children.head.subgoals.isEmpty || p.children.head.subgoals.foldLeft(false)((a: Boolean, b: ProofNode) => a || checkSingleAlternative(b))
    else
      true

  "Tactics (weakSeqT)*" should "produce a proof with no alternatives" in {
    val tactic = ((AxiomCloseT ~ findPosSucc(indecisive(true, false)) ~ findPosAnte(indecisive(true, false, true)))*)
    val r = tryTactic(tactic)
    require(checkSingleAlternative(r) == true, "The proof should not have alternatives")
  }

  "Tactics (eitherT)*" should "produce a proof with no alternatives" in {
    val tactic = ((AxiomCloseT | findPosSucc(indecisive(true, false)) | findPosAnte(indecisive(true, false, true)))*)
    val r = tryTactic(tactic)
    require(checkSingleAlternative(r) == true, "The proof should not have alternatives")
  }
  
  "Tactics (propositional)" should "prove A->A for any A" in {
    val tactic = indecisive(false, false, true)
    val A = new RandomFormula().nextFormula(5)
    val formula = Imply(A, A)
    //@TODO tryProve(formula, tactic) should be (provable)
  }

  it should "prove A->(B->A) for any A,B" in {
    val tactic = indecisive(false, false, true)
    val A = new RandomFormula().nextFormula(5)
    val B = new RandomFormula().nextFormula(5)
    val formula = Imply(A, Imply(B, A))
    //@TODO tryProve(formula, tactic) should be (provable)
  }
}
