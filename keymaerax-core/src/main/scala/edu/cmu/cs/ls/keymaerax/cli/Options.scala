/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.core.BaseVariable
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration

// TODO Convert to Scala 3 enum
sealed trait Command
object Command {
  // General commands
  case object Help extends Command
  case object License extends Command
  // Core commands
  case object Setup extends Command
  case object Prove extends Command
  case class Parse(value: String) extends Command
  case class BParse(value: String) extends Command
  case object Convert extends Command
  case object Grade extends Command
  // Webui commands
  case object Codegen extends Command
  case object Modelplex extends Command
  case object Repl extends Command
  case object Ui extends Command

  // TODO Remove these
  val UiFlag = "-ui"
  val FlagNames: Seq[String] = Seq(
    // General commands
    "help",
    "license",
    // Core commands
    "setup",
    "prove",
    "parse",
    "bparse",
    "convert",
    "grade",
    // Webui commands
    "codegen",
    "modelplex",
    "repl",
    "ui",
  )
}

case class Options(
    // Special options
    commandLine: Option[String] = None,
    command: Option[Command] = None,
    // Options specified using flags
    conjecture: Option[String] = None,
    conversion: Option[String] = None,
    debug: Option[Boolean] = None,
    dnf: Option[Boolean] = None,
    exportanswers: Option[Boolean] = None,
    fallback: Option[String] = None,
    in: Option[String] = None,
    interactive: Option[Boolean] = None,
    interval: Option[Boolean] = None,
    isar: Option[Boolean] = None,
    jlink: Option[String] = None,
    jlinkinterface: Option[String] = None,
    jlinktcpip: Option[String] = None,
    lax: Option[Boolean] = None,
    mathkernel: Option[String] = None,
    model: Option[String] = None,
    monitor: Option[Symbol] = None,
    open: Option[String] = None,
    out: Option[String] = None,
    parallelqe: Option[String] = None,
    parserClass: Option[String] = None,
    proofStatisticsPrinter: Option[String] = None,
    ptOut: Option[String] = None,
    qemethod: Option[String] = None,
    quantitative: Option[Boolean] = None,
    sandbox: Option[Boolean] = None,
    scaladefs: Option[String] = None,
    skiponparseerror: Option[Boolean] = None,
    tactic: Option[String] = None,
    tacticName: Option[String] = None,
    timeout: Option[Long] = None,
    tool: Option[String] = None,
    vars: Option[Array[BaseVariable]] = None,
    verbose: Option[Boolean] = None,
    verify: Option[Boolean] = None,
    z3Path: Option[String] = None,
) {
  def toToolConfig: ToolConfiguration = ToolConfiguration(
    tool = this.tool,
    mathKernel = this.mathkernel,
    jlinkLibDir = this.jlink,
    tcpip = None,
    z3Path = this.z3Path,
  )
}
