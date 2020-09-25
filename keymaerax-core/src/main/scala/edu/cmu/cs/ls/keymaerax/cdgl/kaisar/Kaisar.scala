/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof._
import fastparse._
import edu.cmu.cs.ls.keymaerax.core._
import fastparse.Parsed.{Failure, Success}
import fastparse.internal.Util


/** Entry-point for Kaisar proof checker, which parses a proof and applies all passes in correct order */
object Kaisar {
  private val MAX_CHAR = 80 - "...".length

  // Parse string [[s]] as a Kaisar proof, with additional error pretty-printing / locating
  // @TODO: Factor into parser. Public-ish for testing reasons
  private[keymaerax] def parseProof(s: String): Statement =
    parse(s, ProofParser.statement(_), verboseFailures = true) match {
      case x: Success[Statement] =>
        if (x.index < s.length) {
          val snippet = if (x.index < MAX_CHAR) s.take(x.index) else "..." + s.take(x.index).takeRight(MAX_CHAR)
          val (line, col) = KaisarProgramParser.prettyIndex(x.index, s)
          val msg = s"Could not parse entire input, failed after ($line, $col):\n\t$snippet"
          println(msg)
          println("Displaying nested error message, error location not meaningful.")
          print("Nested ") // prints as "Nested Parse error"
          try {
            val rest = s.drop(x.index)
            parseProof(rest)
            throw KaisarParseException(msg = msg, location = Some(x.index), source = s)
          } catch {
            case e: Throwable => throw KaisarParseException(msg = msg, location = Some(x.index), source = s)
          }
        }
        x.value
      case x: Failure =>
        val exn = KaisarParseException(trace = Some(x.extra.trace(enableLogging = true)), location = Some(x.index), source = s, msg = x.msg)
        println(exn.toString)
        println("\n")
        throw exn
    }

  def result(pf: String): (Statement, Formula) = {
    // Pass name used to print more informative error messages
    var currentPass = "parser"
    try {
      val in = parseProof(pf)
      // Apply all proof transformation and checking passes, and recover error messages if necessary
      try {
        currentPass = "elaboration"
        val sel = new ElaborationPass()(in)
        currentPass = "SSA"
        val ssa = SSAPass(sel)
        currentPass = "deterritorialize"
        val dt = DeterritorializePass(ssa)
        currentPass = "proofChecker"
        val (s, ff) = ProofChecker(Context.empty, dt)
        (s.s, ff)
      } catch {
        case le: LocatedException =>
          def snippetFor(s: ASTNode) = {
            val str = s.toString
            if (str.length < MAX_CHAR) str else "..." + str.take(MAX_CHAR)
          }
          val stmtMessage =
            le match {case ne: NodeException if ne.node != Triv() => s" while checking statement ${snippetFor(ne.node)}" case _ => ""}
          if (le.location.isDefined) {
            val (line, col) = KaisarProgramParser.prettyIndex(le.location.get, pf)
            println(s"Error in pass $currentPass at location ($line, $col)$stmtMessage: \n" + le.msg)
          } else {
            println(s"Error in pass $currentPass$stmtMessage at unknown location$stmtMessage: \n" + le.msg)
          }
          throw le
      }
    } catch {
      case kpe: KaisarParseException => throw kpe
    }
  }

  /** Parse and check proof string [[pf]]
    * @return The formula proved by [[pf]], if any, else raises an exception */
  def apply(pf: String): Formula = result(pf)._2

  /** Parse and check proof string [[pf]]
    * @return The (proved) Kaisar statement resulting from proof [[pf]], if any, else raises an exception */
  def statementProved(pf: String): Statement = result(pf)._1
}
