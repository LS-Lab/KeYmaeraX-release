/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
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
  val MAX_CHAR = 80 - "...".length

  // Translate and check a statement
  def result(kc: Context, in: Statement): (Statement, Formula) = {
    // Apply all proof transformation and checking passes, and recover error messages if necessary
    var currentPass = "elaboration"
    try {
      val sel = new ElaborationPass()(in)
      currentPass = "SSA"
      val ssa = SSAPass(sel)
      currentPass = "deterritorialize"
      val dt = DeterritorializePass(ssa)
      currentPass = "proofChecker"
      val (s, ff) = ProofChecker(kc, dt)
      (s.s, ff)
    } catch {
      case le: LocatedException =>
        def snippetFor(s: ASTNode) = {
          val str = s.toString
          if (str.length < MAX_CHAR) str else "..." + str.take(MAX_CHAR)
        }
        val proofText = ProofOptions.proofText.getOrElse("<unknown>")
        val stmtMessage = le match {
          case ne: NodeException if ne.node != Triv() => s" while checking statement ${snippetFor(ne.node)}"
          case _ => ""
        }
        if (le.location.isDefined) {
          val (line, col) = KaisarProgramParser.prettyIndex(le.location.get, proofText)
          println(s"Error in pass $currentPass at location ($line, $col)$stmtMessage: \n" + le.msg)
        } else { println(s"Error in pass $currentPass$stmtMessage at unknown location$stmtMessage: \n" + le.msg) }
        throw le
    }
  }

  /**
   * Parse and check single proof string [[pf]]
   * @return
   *   The formula proved by [[pf]], if any, else raises an exception
   */
  def single(pf: String): (Statement, Formula) = {
    ProofOptions.proofText = Some(pf)
    val s = KaisarProgramParser.parseSingle(pf)
    result(Context.empty, s)
  }

  /**
   * Parse and check proof string [[pf]]
   * @return
   *   The (proved) Kaisar statement resulting from proof [[pf]], if any, else raises an exception
   */
  def statementProved(pf: String): Statement = single(pf)._1
}
