/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.info.FullNameAndVersion
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration
import scopt.OParser

// TODO Convert to Scala 3 enum
sealed trait Command
object Command {
  // Core commands
  case object Setup extends Command
  case object Prove extends Command
  case class Parse(value: String = null) extends Command
  case class BParse(value: String = null) extends Command
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
    args: Seq[String],
    help: Boolean = false,
    license: Boolean = false,
    launch: Boolean = false,
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
    vars: Option[Seq[String]] = None,
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

object Options {
  private val LaunchFlagName = "launch"
  val LaunchFlag = s"--$LaunchFlagName"

  def parseArgs(name: String, args: Seq[String]): Options = {
    val builder = OParser.builder[Options]
    import builder._

    val parser = OParser.sequence(
      programName(name),
      head(FullNameAndVersion),
      opt[Unit]('h', "help").action((_, o) => o.copy(help = true)),
      opt[Unit]("license").action((_, o) => o.copy(license = true)),
      opt[Unit](LaunchFlagName).hidden().action((_, o) => o.copy(launch = true)),

      // Options specified using flags
      opt[String]("conjecture").action((x, o) => o.copy(conjecture = Some(x))),
      opt[Unit]("debug").action((_, o) => o.copy(debug = Some(true))),
      opt[Unit]("dnf").action((_, o) => o.copy(dnf = Some(true))),
      opt[Unit]("exportanswers").action((_, o) => o.copy(exportanswers = Some(true))),
      opt[String]("fallback").action((x, o) => o.copy(fallback = Some(x))),
      opt[Unit]("interactive").action((_, o) => o.copy(interactive = Some(true))),
      opt[Unit]("interval").action((_, o) => o.copy(interval = Some(true))),
      opt[Unit]("isar").action((_, o) => o.copy(isar = Some(true))),
      opt[String]("jlink").action((x, o) => o.copy(jlink = Some(x))),
      opt[String]("jlinkinterface")
        .validate(it => if (it == "string" || it == "expr") success else failure("must be 'string' or 'expr'"))
        .action((x, o) => o.copy(jlinkinterface = Some(x))),
      opt[String]("jlinktcpip")
        .validate(it => if (it == "true" || it == "false") success else failure("must be 'true' or 'false'"))
        .action((x, o) => o.copy(jlinktcpip = Some(x))),
      opt[Unit]("lax").action((_, o) => o.copy(lax = Some(true))),
      opt[String]("mathkernel").action((x, o) => o.copy(mathkernel = Some(x))),
      opt[String]("monitor").action((x, o) => o.copy(monitor = Some(Symbol(x)))),
      opt[Unit]("nodebug").action((_, o) => o.copy(debug = Some(false))),
      opt[Unit]("nointerval").action((_, o) => o.copy(interval = Some(false))),
      opt[String]("open").action((x, o) => o.copy(open = Some(x))),
      opt[String]("out").action((x, o) => o.copy(out = Some(x))),
      opt[String]("parallelqe")
        .validate(it => if (it == "true" || it == "false") success else failure("must be 'true' or 'false'"))
        .action((x, o) => o.copy(parallelqe = Some(x))),
      opt[String]("parserClass").action((x, o) => o.copy(parserClass = Some(x))),
      opt[String]("proofStatistics").action((x, o) => o.copy(proofStatisticsPrinter = Some(x))),
      opt[String]("qemethod")
        .validate(it => if (it == "Reduce" || it == "Resolve") success else failure("must be 'Reduce' or 'Resolve'"))
        .action((x, o) => o.copy(qemethod = Some(x))),
      opt[Unit]("quantitative").action((_, o) => o.copy(quantitative = Some(true))),
      opt[Unit]("sandbox").action((_, o) => o.copy(sandbox = Some(true))),
      opt[String]("savept").action((x, o) => o.copy(ptOut = Some(x))),
      opt[Unit]("skiponparseerror").action((_, o) => o.copy(skiponparseerror = Some(true))),
      opt[Unit]("strict").action((_, o) => o.copy(lax = Some(false))),
      opt[String]("tactic").action((x, o) => o.copy(tactic = Some(x))),
      opt[String]("tacticName").action((x, o) => o.copy(tacticName = Some(x))),
      opt[Long]("timeout").action((x, o) => o.copy(timeout = Some(x))),
      opt[String]("tool").action((x, o) => o.copy(tool = Some(x))),
      opt[Seq[String]]("vars").action((x, o) => o.copy(vars = Some(x))),
      opt[Unit]("verbose").action((_, o) => o.copy(verbose = Some(true))),
      opt[Unit]("verify").action((_, o) => o.copy(verify = Some(true))),
      opt[String]("z3path").action((x, o) => o.copy(z3Path = Some(x))),

      // Core commands
      cmd("setup").action((_, o) => o.copy(command = Some(Command.Setup))),
      cmd("prove")
        .action((_, o) => o.copy(command = Some(Command.Prove)))
        .children(arg[String]("<in>").action((x, o) => o.copy(in = Some(x)))),
      cmd("parse")
        .action((_, o) => o.copy(command = Some(Command.Parse())))
        .children(arg[String]("<value>").action((x, o) => {
          val command = o.command.get.asInstanceOf[Command.Parse]
          o.copy(command = Some(command.copy(value = x)))
        })),
      cmd("bparse")
        .action((_, o) => o.copy(command = Some(Command.BParse())))
        .children(arg[String]("<value>").action((x, o) => {
          val command = o.command.get.asInstanceOf[Command.BParse]
          o.copy(command = Some(command.copy(value = x)))
        })),
      cmd("convert")
        .action((_, o) => o.copy(command = Some(Command.Convert)))
        .children(
          arg[String]("<conversion>").action((x, o) => o.copy(conversion = Some(x))),
          arg[String]("<in>").action((x, o) => o.copy(in = Some(x))),
        ),
      cmd("grade")
        .action((_, o) => o.copy(command = Some(Command.Grade)))
        .children(arg[String]("<in>").action((x, o) => o.copy(in = Some(x)))),

      // Webui commands
      cmd("codegen")
        .action((_, o) => o.copy(command = Some(Command.Codegen)))
        .children(arg[String]("<in>").action((x, o) => o.copy(in = Some(x)))),
      cmd("modelplex")
        .action((_, o) => o.copy(command = Some(Command.Modelplex)))
        .children(arg[String]("<in>").action((x, o) => o.copy(in = Some(x)))),
      cmd("repl")
        .action((_, o) => o.copy(command = Some(Command.Repl)))
        .children(
          arg[String]("<model>").action((x, o) => o.copy(model = Some(x))),
          arg[String]("<tactic>").optional().action((x, o) => o.copy(tactic = Some(x))),
          arg[String]("<scaladefs>").optional().action((x, o) => o.copy(scaladefs = Some(x))),
        ),
      cmd("ui").action((_, o) => o.copy(command = Some(Command.Ui))),
    )

    // When parse() returns None, it failed to parse the arguments
    // and will have already printed some sort of error message.
    val options = OParser.parse(parser, args, Options(args = args)).getOrElse(sys.exit(1))

    if (options.help) {
      println(OParser.usage(parser))
      sys.exit(0)
    }

    if (options.license) {
      println(License.license)
      sys.exit(0)
    }

    options
  }
}
