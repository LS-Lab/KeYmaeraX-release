/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BellePrettyPrinter

import scala.io.Source

/**
  * Computes tactic statistics (e.g., size).
  *
  * @author Stefan Mitsch
  * Created by smitsch on 5/24/17.
  */
object TacticStatistics {
  /** Returns the size of a tactic (its atomic subtactics, +1 for operators *, *n, <, let, doall). */
  def size(t: BelleExpr): Int = t match {
    case SeqTactic(s) => s.map(size).sum
    case EitherTactic(s) => s.map(size).sum
    case SaturateTactic(c) => size(c) + 1
    case RepeatTactic(c, _) => size(c) + 1
    case BranchTactic(c) => c.map(size).sum + 1
    case CaseTactic(c) => c.map(_._2).map(size).sum + 1
    case OnAll(c) => size(c) + 1
    case Let(_, _, c) => size(c) + 1
    case DefTactic(_, c) => size(c)
    case Using(_, c) => size(c)
    case _ => 1
  }

  /** Returns the number of atomic tactics of `t` (as listed in the script, not as executed) */
  def atomicSteps(t: BelleExpr): Int = t match {
    case SeqTactic(s) => s.map(size).sum
    case EitherTactic(s) => s.map(size).sum
    case SaturateTactic(c) => size(c)
    case RepeatTactic(c, _) => size(c)
    case BranchTactic(c) => c.map(size).sum
    case CaseTactic(c) => c.map(_._2).map(size).sum
    case OnAll(c) => size(c)
    case Let(_, _, c) => size(c)
    case DefTactic(_, c) => size(c)
    case Using(_, c) => size(c)
    case _ => 1
  }

  /** Returns the tactic LOC. */
  def lines(t: BelleExpr): Int = Source.fromString(BellePrettyPrinter(t)).getLines().size
}
