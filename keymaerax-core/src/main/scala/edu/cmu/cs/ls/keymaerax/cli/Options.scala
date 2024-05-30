/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX.OptionMap
import edu.cmu.cs.ls.keymaerax.core.BaseVariable

case class Options(
    commandLine: Option[String] = None,
    mode: Option[String] = None,
    conjecture: Option[String] = None,
    in: Option[String] = None,
    exportanswers: Option[Boolean] = None,
    skiponparseerror: Option[Boolean] = None,
    out: Option[String] = None,
    ptOut: Option[String] = None,
    conversion: Option[String] = None,
    tactic: Option[String] = None,
    tacticName: Option[String] = None,
    tool: Option[String] = None,
    verbose: Option[Boolean] = None,
    proofStatisticsPrinter: Option[String] = None,
    mathkernel: Option[String] = None,
    jlink: Option[String] = None,
    z3Path: Option[String] = None,
    timeout: Option[Long] = None,
    sandbox: Option[Boolean] = None,
    isar: Option[Boolean] = None,
    quantitative: Option[Boolean] = None,
    scaladefs: Option[String] = None,
    model: Option[String] = None,
    fallback: Option[String] = None,
    vars: Option[Array[BaseVariable]] = None,
    monitor: Option[Symbol] = None,
    interactive: Option[Boolean] = None,
    interval: Option[Boolean] = None,
    dnf: Option[Boolean] = None,
) {
  def toOptionMap: OptionMap = List(
    this.commandLine.map(Symbol("commandLine") -> _),
    this.mode.map(Symbol("mode") -> _),
    this.conjecture.map(Symbol("conjecture") -> _),
    this.in.map(Symbol("in") -> _),
    this.exportanswers.map(Symbol("exportanswers") -> _),
    this.skiponparseerror.map(Symbol("skiponparseerror") -> _),
    this.out.map(Symbol("out") -> _),
    this.ptOut.map(Symbol("ptOut") -> _),
    this.conversion.map(Symbol("conversion") -> _),
    this.tactic.map(Symbol("tactic") -> _),
    this.tacticName.map(Symbol("tacticName") -> _),
    this.tool.map(Symbol("tool") -> _),
    this.verbose.map(Symbol("verbose") -> _),
    this.proofStatisticsPrinter.map(Symbol("proofStatisticsPrinter") -> _),
    this.mathkernel.map(Symbol("mathkernel") -> _),
    this.jlink.map(Symbol("jlink") -> _),
    this.z3Path.map(Symbol("z3Path") -> _),
    this.timeout.map(Symbol("timeout") -> _),
    this.sandbox.map(Symbol("sandbox") -> _),
    this.isar.map(Symbol("isar") -> _),
    this.quantitative.map(Symbol("quantitative") -> _),
    this.scaladefs.map(Symbol("scaladefs") -> _),
    this.model.map(Symbol("model") -> _),
    this.fallback.map(Symbol("fallback") -> _),
    this.vars.map(Symbol("vars") -> _),
    this.monitor.map(Symbol("monitor") -> _),
    this.interactive.map(Symbol("interactive") -> _),
    this.interval.map(Symbol("interval") -> _),
    this.dnf.map(Symbol("dnf") -> _),
  ).flatten.toMap
}
