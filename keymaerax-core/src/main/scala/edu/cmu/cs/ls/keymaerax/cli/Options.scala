/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.core.BaseVariable
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration

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
    verify: Option[Boolean] = None,
    open: Option[String] = None,
) {
  def toToolConfig: ToolConfiguration = ToolConfiguration(
    tool = this.tool,
    mathKernel = this.mathkernel,
    jlinkLibDir = this.jlink,
    tcpip = None,
    z3Path = this.z3Path,
  )
}
