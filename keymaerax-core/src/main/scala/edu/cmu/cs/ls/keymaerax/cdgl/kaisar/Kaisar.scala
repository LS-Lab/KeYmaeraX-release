/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import fastparse._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProofChecker.ProofCheckException
import fastparse.Parsed.{Failure, Success}

import scala.collection.immutable.StringOps


/** Entry-point for Kaisar proof checker, which parses a proof and applies all passes in correct order */
object Kaisar {

  private def prettyIndex(index: Int, input: String): (Int, Int) = {
    var lines = (input:StringOps).lines.toList
    var colIndex = index
    var lineIndex = 0
    // @TODO: Could be off by one
    while (lines.nonEmpty && colIndex >= lines.head.length) {
      lineIndex = lineIndex + 1
      colIndex = colIndex - lines.head.length
      lines = lines.tail
    }
    (lineIndex, colIndex)
  }

  private def p[T](s: String, parser: P[_] => P[T]): T =
    parse(s, parser) match {
      case x: Success[T] =>
        if (x.index < s.length) {
          val MAX_CHAR = 80 - "...".length
          val snippet = if (x.index < MAX_CHAR) s.take(x.index) else "..." + s.take(x.index).takeRight(MAX_CHAR)
          val (line, col) = prettyIndex(x.index, s)
          val msg = s"Could not parse entire input, only parsed up through ($line, $col):\n$snippet"
          println(msg)
          println("DEBUG: Parsing (failed) remaining input to construct error: ")
          try {
            val rest = s.drop(x.index)
            p(rest, parser)
            throw new Exception(msg)
          } catch {
            case e: Throwable => throw new Exception(msg, e)
          }
        }
        x.value
      case x: Failure => throw new Exception(x.trace().toString)
    }

  def apply(pf: String): Formula = {
    var currentPass = "parser"
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
          val (line, col) = prettyIndex(pce.location.get, pf)
          println(s"Error in pass $currentPass at location ($line, $col): ")
        } else {
          println(s"Error in pass $currentPass at unknown location")
        }
        println(pce.str)
        throw pce
    }
  }
}
