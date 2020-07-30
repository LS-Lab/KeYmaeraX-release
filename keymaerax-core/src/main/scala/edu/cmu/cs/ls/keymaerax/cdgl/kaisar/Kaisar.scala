package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import fastparse._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.Context._
import edu.cmu.cs.ls.keymaerax.infrastruct.{FormulaTools, UnificationMatch}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import fastparse.Parsed.{Failure, Success}




object Kaisar {

  private def p[T](s: String, parser: P[_] => P[T]): T =
    parse(s, parser) match {
      case x: Success[T] => x.value
      case x: Failure => throw new Exception(x.trace().toString)
    }

  def apply(pf: String): Formula = {
    val in = p(pf, ProofParser.statement(_))
    val sel = SelectorEliminationPass(in)
    val ssa = SSAPass(sel)
    val (s, ff) = ProofChecker(Context.empty, ssa)
    ff
  }
}
