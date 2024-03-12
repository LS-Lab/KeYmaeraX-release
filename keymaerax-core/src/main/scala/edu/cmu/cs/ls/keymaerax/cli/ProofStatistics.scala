/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

/** Collects proof statistics. */
case class ProofStatistics(
    name: String,
    tacticName: String,
    status: String,
    witness: Option[ProvableSig],
    timeout: Long,
    duration: Long,
    qeDuration: Long,
    rcfDuration: Long,
    proofSteps: Int,
    tacticSize: Int,
) {

  /** Prints a statistics summary string. */
  def summary: String = s"""Proof Statistics ($name $status, with tactic $tacticName and time budget [s] $timeout)
                           |Duration [ms]: $duration
                           |QE [ms]: $qeDuration, RCF [ms]: $rcfDuration
                           |Proof steps: $proofSteps
                           |Tactic size: $tacticSize""".stripMargin

  /** Short single-line summary. */
  override def toString: String =
    s"${status.toUpperCase} $name: tactic=$tacticName,tacticsize=$tacticSize,budget=$timeout[s],duration=$duration[ms],qe=$qeDuration[ms],rcf=$rcfDuration,steps=$proofSteps"
}
