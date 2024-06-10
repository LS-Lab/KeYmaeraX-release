/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.concurrent.duration.Duration

/** Collects proof statistics. */
case class ProofStatistics(
    name: String,
    tacticName: String,
    status: String,
    witness: Option[ProvableSig],
    timeout: Duration,
    duration: Long,
    qeDuration: Long,
    rcfDuration: Long,
    proofSteps: Int,
    tacticSize: Int,
) {

  /** Short single-line summary. */
  override def toString: String =
    s"${status.toUpperCase} $name: tactic=$tacticName,tacticsize=$tacticSize,budget=$timeout,duration=$duration[ms],qe=$qeDuration[ms],rcf=$rcfDuration,steps=$proofSteps"
}
