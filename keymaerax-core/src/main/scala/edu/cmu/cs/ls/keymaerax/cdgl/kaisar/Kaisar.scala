/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.KaisarParseException
import fastparse._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProofChecker.ProofCheckException
import fastparse.Parsed.{Failure, Success}


/** Entry-point for Kaisar proof checker, which parses a proof and applies all passes in correct order */
object Kaisar {
  private def p[T](s: String, parser: P[_] => P[T]): T =
    parse(s, parser, verboseFailures = true) match {
      case x: Success[T] =>
        if (x.index < s.length) {
          val MAX_CHAR = 80 - "...".length
          val snippet = if (x.index < MAX_CHAR) s.take(x.index) else "..." + s.take(x.index).takeRight(MAX_CHAR)
          val (line, col) = KaisarProgramParser.prettyIndex(x.index, s)
          val msg = s"Could not parse entire input, failed after ($line, $col):\n\t$snippet"
          println(msg)
          println("Displaying nested error message, error location not meaningful.")
          print("Nested ") // prints as "Nested Parse error"
          try {
            x.toString()
            val rest = s.drop(x.index)
            p(rest, parser)
            throw new Exception(msg)
          } catch {
            case e: Throwable => throw new Exception(msg, e)
          }
        }
        x.value
      case x: Failure =>
        val exn = KaisarParseException(Some(x.extra.trace(enableLogging = true)))
        println("Parse error: " + exn.toString)
        println("\n")
        throw exn
    }

  def apply(pf: String): Formula = {
    var currentPass = "parser"
    try {
      val in = p(pf, ProofParser.statement(_))
      try {
        currentPass = "selectorElimination"
        val sel = new SelectorEliminationPass()(in)
        currentPass = "SSA"
        val ssa = SSAPass(sel)
        currentPass = "deterritorialize"
        val dt = DeterritorializePass(ssa)
        currentPass = "proofChecker"
        val (s, ff) = ProofChecker(Context.empty, dt)
        ff
      } catch {
        case pce: ProofCheckException =>
          if (pce.location.isDefined) {
            val (line, col) = KaisarProgramParser.prettyIndex(pce.location.get, pf)
            println(s"Error in pass $currentPass at location ($line, $col): ")
          } else {
            println(s"Error in pass $currentPass at unknown location")
          }
          throw pce
      }
    } catch {
      case kpe: KaisarParseException => throw kpe
    }
  }
}
