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
    command: Option[Command] = None,
    commandLine: Option[String] = None,
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
    parserClass: Option[String] = None,
    jlinkinterface: Option[String] = None,
    qemethod: Option[String] = None,
    jlinktcpip: Option[String] = None,
    parallelqe: Option[String] = None,
    lax: Option[Boolean] = None,
    debug: Option[Boolean] = None,
) {
  def toToolConfig: ToolConfiguration = ToolConfiguration(
    tool = this.tool,
    mathKernel = this.mathkernel,
    jlinkLibDir = this.jlink,
    tcpip = None,
    z3Path = this.z3Path,
  )
}
