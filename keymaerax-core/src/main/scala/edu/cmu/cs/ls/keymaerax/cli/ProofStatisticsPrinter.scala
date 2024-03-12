/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

trait ProofStatisticsPrinter {

  /** Prints the proof statistics */
  def print(ps: List[ProofStatistics]): String
}

abstract class BaseProofStatisticsPrinter extends ProofStatisticsPrinter {

  /** Prints the CSV header. */
  def csvHeader: String

  /** Prints a single entry to CSV. */
  def toCsv(ps: ProofStatistics): String

  /** @inheritdoc */
  override def print(ps: List[ProofStatistics]): String = csvHeader + "\n" + ps.map(toCsv).mkString("\n")
}

/** Prints proof statistics to CSV format. */
object CsvProofStatisticsPrinter extends BaseProofStatisticsPrinter {

  /** @inheritdoc */
  override def csvHeader: String =
    "Name,Tactic,Status,Timeout,Duration,QE duration,RCF duration,Proof steps,Tactic size"

  /** @inheritdoc */
  override def toCsv(ps: ProofStatistics): String = s"${ps.name},${ps.tacticName},${ps.status},${ps.timeout * 1000},${ps
      .duration},${ps.qeDuration},${ps.rcfDuration},${ps.proofSteps},${ps.tacticSize}"
}

/** Prints proof statistics to ARCH NLN CSV format. */
object ArchNLNCsvProofStatisticsPrinter extends BaseProofStatisticsPrinter {

  /** @inheritdoc */
  override def csvHeader: String = "benchmark,instance,result,time,accuracy,timesteps"

  /** @inheritdoc */
  override def toCsv(ps: ProofStatistics): String =
    s"${ps.name},${ps.tacticName},${ps.status},${ps.duration},0,${ps.proofSteps}"
}

/** Prints proof statistics to ARCH HSTP CSV format. */
object ArchHSTPCsvProofStatisticsPrinter extends BaseProofStatisticsPrinter {

  /** @inheritdoc */
  override def csvHeader: String = "benchmark,instance,result,time"

  /** @inheritdoc */
  override def toCsv(ps: ProofStatistics): String = {
    val _ :: category :: instance = ps.name.split("/").toList
    s"$category,${instance.mkString("/")},${ps.status},${ps.duration}"
  }
}
