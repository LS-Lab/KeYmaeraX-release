package edu.cmu.cs.ls.keymaera.tests

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.parser.KeYmaeraPrettyPrinter

object TermTests {

  def test = {
      //val p = new FormulaName("p")
      val p = new PredicateConstant("p")
      val q = new PredicateConstant("q")
      //val q = new FormulaName("q")
      val i = Imply(p, q)
      val i2 = Imply(q, i)
      println(i)
      val r = new RootNode(new Sequent(Nil, Vector(), Vector(i2)))
      val pos = new Position(false, 0)
      val pos2 = new Position(true, 0)
      val c = r(ImplyRight, pos)
      for(n <- c) {
        val c2 = n(ImplyRight, pos)
        for(n2 <- c2) {
          val end = n2(AxiomClose(pos2), pos)
          println(end)
        }
      }
  }

  def test2 = {
    val p = new PredicateConstant("p")
    val q = new PredicateConstant("q")
    val i = Imply(p, q)
    val i2 = Imply(q, i)
    println(KeYmaeraPrettyPrinter.stringify(i2))
    val r = new RootNode(new Sequent(Nil, Vector(), Vector(i2)))
    println(r.isClosed)
    println(print(r))
    val tactic: Tactic = (ImplyRightFindT*) & ImplyLeftFindT & AxiomCloseT
    tactic(r, new Limit(None, None))
    println(print(r))
    r.isClosed
  }

  def print(l: Seq[Formula]): String = (for(f <- l) yield KeYmaeraPrettyPrinter.stringify(f)).foldLeft("")(_ + "," + _)
  def print(s: Sequent): String = print(s.ante) + " ==> " + print(s.succ)
  def print(p: ProofNode): String = print(p.sequent) + "\n" + p.children.map(print).foldLeft("")(_ + "," + _)
  def print(ps: ProofStep): String = ps.rule.toString + " -- [" + ps.subgoals.map(print) + "]"

}

// vim: set ts=4 sw=4 et:
