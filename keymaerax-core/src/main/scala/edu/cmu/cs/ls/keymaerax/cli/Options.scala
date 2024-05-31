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
      opt[Unit]('h', "help").action((_, o) => o.copy(help = true)).text("Display this usage information"),
      opt[Unit]("license")
        .action((_, o) => o.copy(license = true))
        .text("Show license agreement for using this software"),
      opt[Unit](LaunchFlagName)
        .action((_, o) => o.copy(launch = true))
        .text("use present JVM instead of launching one with a bigger stack"),

      // Options specified using flags
      opt[String]("conjecture").action((x, o) => o.copy(conjecture = Some(x))),
      opt[Unit]("debug").action((_, o) => o.copy(debug = Some(true))).text("use debug mode with exhaustive messages"),
      opt[Unit]("nodebug")
        .action((_, o) => o.copy(debug = Some(false)))
        .text("disable debug mode to suppress intermediate messages"),
      opt[Unit]("dnf").action((_, o) => o.copy(dnf = Some(true))),
      opt[Unit]("exportanswers").action((_, o) => o.copy(exportanswers = Some(true))),
      opt[String]("fallback").action((x, o) => o.copy(fallback = Some(x))),
      opt[Unit]("interactive").action((_, o) => o.copy(interactive = Some(true))),
      opt[Unit]("interval")
        .action((_, o) => o.copy(interval = Some(true)))
        .text("guard reals by interval arithmetic in floating point (recommended)"),
      opt[Unit]("nointerval")
        .action((_, o) => o.copy(interval = Some(false)))
        .text("skip interval arithmetic presuming no floating point errors"),
      opt[Unit]("isar").action((_, o) => o.copy(isar = Some(true))),
      opt[String]("jlink")
        .action((x, o) => o.copy(jlink = Some(x)))
        .valueName("path/to/jlinkNativeLib")
        .text("path to Mathematica J/Link library directory"),
      opt[String]("jlinkinterface")
        .validate(it => if (it == "string" || it == "expr") success else failure("must be 'string' or 'expr'"))
        .action((x, o) => o.copy(jlinkinterface = Some(x)))
        .valueName("string|expr")
        .text(
          """whether to send Mathematica commands as
            |strings (more robust) or as
            |expr (supports larger queries)
            |Default: string (unless configured in keymaerax.conf)
            |""".stripMargin
        ),
      opt[String]("jlinktcpip")
        .validate(it => if (it == "true" || it == "false") success else failure("must be 'true' or 'false'"))
        .action((x, o) => o.copy(jlinktcpip = Some(x)))
        .valueName("true|false")
        .text(
          """whether to connect to Mathematica with
            |process communication or
            |over TCP/IP (more robust)
            |Default: false (unless configured in keymaerax.conf)
            |""".stripMargin
        ),
      opt[Unit]("lax")
        .action((_, o) => o.copy(lax = Some(true)))
        .text("use lax mode with more flexible parser, printer, prover etc."),
      opt[String]("mathkernel")
        .action((x, o) => o.copy(mathkernel = Some(x)))
        .valueName("MathKernel(.exe)")
        .text("path to Mathematica kernel executable"),
      opt[String]("monitor")
        .action((x, o) => o.copy(monitor = Some(Symbol(x))))
        .valueName("ctrl|model")
        .text("what kind of monitor to generate with ModelPlex"),
      opt[String]("open").action((x, o) => o.copy(open = Some(x))),
      opt[String]("out").action((x, o) => o.copy(out = Some(x))),
      opt[String]("parallelqe")
        .validate(it => if (it == "true" || it == "false") success else failure("must be 'true' or 'false'"))
        .action((x, o) => o.copy(parallelqe = Some(x)))
        .valueName("true|false")
        .text(
          """whether to attempt multiple QE alternatives in parallel
            |Default: false (unless configured in keymaerax.conf)
            |""".stripMargin
        ),
      opt[String]("parserClass").action((x, o) => o.copy(parserClass = Some(x))),
      opt[String]("proofStatistics").action((x, o) => o.copy(proofStatisticsPrinter = Some(x))),
      opt[String]("qemethod")
        .validate(it => if (it == "Reduce" || it == "Resolve") success else failure("must be 'Reduce' or 'Resolve'"))
        .action((x, o) => o.copy(qemethod = Some(x)))
        .valueName("Reduce|Resolve")
        .text(
          """whether to use
            |Reduce (solves equations and eliminates quantifiers) or
            |Resolve (eliminates quantifiers)
            |Default: Reduce (unless configured in keymaerax.conf)
            |""".stripMargin
        ),
      opt[Unit]("quantitative").action((_, o) => o.copy(quantitative = Some(true))),
      opt[Unit]("sandbox").action((_, o) => o.copy(sandbox = Some(true))),
      opt[String]("savept")
        .action((x, o) => o.copy(ptOut = Some(x)))
        .valueName("path")
        .text("export proof term s-expression from -prove to given path"),
      opt[Unit]("skiponparseerror").action((_, o) => o.copy(skiponparseerror = Some(true))),
      opt[Unit]("strict")
        .action((_, o) => o.copy(lax = Some(false)))
        .text("use strict mode with no flexibility in prover"),
      opt[String]("tactic").action((x, o) => o.copy(tactic = Some(x))),
      opt[String]("tacticName").action((x, o) => o.copy(tacticName = Some(x))),
      opt[Long]("timeout")
        .action((x, o) => o.copy(timeout = Some(x)))
        .text("how many seconds to try proving before giving up, forever if <=0"),
      opt[String]("tool")
        .action((x, o) => o.copy(tool = Some(x)))
        .valueName("mathematica|z3")
        .text("choose which tool to use for real arithmetic"),
      opt[Seq[String]]("vars")
        .action((x, o) => o.copy(vars = Some(x)))
        .valueName("var1,var2,..,varn")
        .text("use ordered list of variables, treating others as constant functions"),
      opt[Unit]("verbose").action((_, o) => o.copy(verbose = Some(true))),
      opt[Unit]("verify").action((_, o) => o.copy(verify = Some(true))),
      opt[String]("z3path")
        .action((x, o) => o.copy(z3Path = Some(x)))
        .valueName("path/to/z3")
        .text("path to Z3 executable"),

      // Core commands
      note(""),
      cmd("setup")
        .action((_, o) => o.copy(command = Some(Command.Setup)))
        .text("initialize the configuration and lemma cache"),
      note(""),
      cmd("prove")
        .action((_, o) => o.copy(command = Some(Command.Prove)))
        .text("run prover on given archive of models or proofs")
        .children(arg[String]("file.kyx").action((x, o) => o.copy(in = Some(x)))),
      note(""),
      cmd("parse")
        .action((_, o) => o.copy(command = Some(Command.Parse())))
        .text("return error code 0 if the given model file parses")
        .children(arg[String]("<value>").action((x, o) => {
          val command = o.command.get.asInstanceOf[Command.Parse]
          o.copy(command = Some(command.copy(value = x)))
        })),
      note(""),
      cmd("bparse")
        .action((_, o) => o.copy(command = Some(Command.BParse())))
        .text("return error code 0 if given bellerophon tactic file parses")
        .children(arg[String]("<value>").action((x, o) => {
          val command = o.command.get.asInstanceOf[Command.BParse]
          o.copy(command = Some(command.copy(value = x)))
        })),
      note(""),
      cmd("convert")
        .action((_, o) => o.copy(command = Some(Command.Convert)))
        .text("model and tactic conversions")
        .children(
          arg[String]("stripHints|kyx2mat|kyx2smt|mat2kyx|mat2smt|smt2kyx|smt2mat")
            .action((x, o) => o.copy(conversion = Some(x))),
          arg[String]("file.kyx").action((x, o) => o.copy(in = Some(x))),
        ),
      note(""),
      cmd("grade")
        .action((_, o) => o.copy(command = Some(Command.Grade)))
        .children(arg[String]("<in>").action((x, o) => o.copy(in = Some(x)))),

      // Webui commands
      note(""),
      cmd("codegen")
        .action((_, o) => o.copy(command = Some(Command.Codegen)))
        .text("generate executable C code from a model file")
        .children(arg[String]("file.kym").action((x, o) => o.copy(in = Some(x)))),
      note(""),
      cmd("modelplex")
        .action((_, o) => o.copy(command = Some(Command.Modelplex)))
        .text("synthesize a monitor from a model by proof with the ModelPlex tactic")
        .children(arg[String]("file.kyx").action((x, o) => o.copy(in = Some(x)))),
      note(""),
      cmd("repl")
        .action((_, o) => o.copy(command = Some(Command.Repl)))
        .text("prove a model interactively from a command line REPL")
        .children(
          arg[String]("<model>").action((x, o) => o.copy(model = Some(x))),
          arg[String]("<tactic>").optional().action((x, o) => o.copy(tactic = Some(x))),
          arg[String]("<scaladefs>").optional().action((x, o) => o.copy(scaladefs = Some(x))),
        ),
      note(""),
      cmd("ui").action((_, o) => o.copy(command = Some(Command.Ui))).text("start web user interface"),
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
