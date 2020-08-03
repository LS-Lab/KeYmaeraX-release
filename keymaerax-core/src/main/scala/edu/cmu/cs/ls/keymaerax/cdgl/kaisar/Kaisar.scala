/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import fastparse._
import edu.cmu.cs.ls.keymaerax.core._
import fastparse.Parsed.{Failure, Success}


/** Entry-point for Kaisar proof checker, which parses a proof and applies all passes in correct order */
object Kaisar {

  private def p[T](s: String, parser: P[_] => P[T]): T =
    parse(s, parser) match {
      case x: Success[T] => x.value
      case x: Failure => throw new Exception(x.trace().toString)
    }

  def apply(pf: String): Formula = {
    val in = p(pf, ProofParser.statement(_))
    val sel = new SelectorEliminationPass()(in)
    val ssa = SSAPass(sel)
    val dt = DeterritorializePass(ssa)
    val (s, ff) = ProofChecker(Context.empty, dt)
    ff
  }
}
