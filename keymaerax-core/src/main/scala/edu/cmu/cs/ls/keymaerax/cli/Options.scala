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
  case class Prove(
      in: String = null,
      out: Option[String] = None,
      ptOut: Option[String] = None,
      conjecture: Option[String] = None,
      tactic: Option[String] = None,
      tacticName: Option[String] = None,
      timeout: Long = 0,
      verbose: Boolean = false,
      statistics: Option[String] = None,
  ) extends Command
  case class Parse(in: String = null) extends Command
  case class BParse(in: String = null) extends Command
  case class Convert(conversion: String = null, in: String = null, out: Option[String] = None) extends Command
  case class Grade(
      in: String = null,
      out: Option[String] = None,
      exportAnswers: Boolean = false,
      skipOnParseError: Boolean = false,
  ) extends Command
  // Webui commands
  case class Codegen(
      in: String = null,
      out: Option[String] = None,
      quantitative: Boolean = false,
      interval: Boolean = true,
      vars: Option[Seq[String]] = None,
  ) extends Command
  case class Modelplex(
      in: String = null,
      out: Option[String] = None,
      ptOut: Option[String] = None,
      vars: Option[Seq[String]] = None,
      verify: Boolean = false,
  ) extends Command
  case class Repl(tactic: Option[String] = None) extends Command
  case object Ui extends Command
}

case class Options(
    // Special options
    name: String,
    args: Seq[String],
    help: Boolean = false,
    license: Boolean = false,
    launch: Boolean = false,
    command: Option[Command] = None,
    // Options specified using flags
    debug: Option[Boolean] = None,
    fallback: Option[String] = None,
    jlink: Option[String] = None,
    jlinkinterface: Option[String] = None,
    jlinktcpip: Option[String] = None,
    lax: Option[Boolean] = None,
    mathkernel: Option[String] = None,
    model: Option[String] = None,
    monitor: Option[Symbol] = None,
    open: Option[String] = None,
    parallelqe: Option[String] = None,
    parserClass: Option[String] = None,
    qemethod: Option[String] = None,
    sandbox: Option[Boolean] = None,
    scaladefs: Option[String] = None,
    tool: Option[String] = None,
    z3Path: Option[String] = None,
) {

  /** Helper function to make updating command-specific options easier. */
  private def updateCommand[C <: Command](update: C => C): Options = this
    .copy(command = Some(update(this.command.get.asInstanceOf[C])))

  def toToolConfig: ToolConfiguration = ToolConfiguration(
    tool = this.tool,
    mathKernel = this.mathkernel,
    jlinkLibDir = this.jlink,
    tcpip = None,
    z3Path = this.z3Path,
  )

  def printUsageAndExitWithError(): Unit = {
    println(OParser.usage(Options.parser(name)))
    sys.exit(1)
  }
}

object Options {
  private val LaunchFlagName = "launch"
  val LaunchFlag = s"--$LaunchFlagName"

  private def wrap(text: String): String = {
    // The left column of the help output (including the space separating the columns) has a width of 27 characters.
    TextWrapper.wrap(text, maxWidth = 80 - 27)
  }

  private def parser(name: String): OParser[Unit, Options] = {
    val builder = OParser.builder[Options]
    import builder._

    OParser.sequence(
      programName(name),
      head(FullNameAndVersion),
      opt[Unit]('h', "help").action((_, o) => o.copy(help = true)).text(wrap("Show this usage information.")),
      opt[Unit]("license")
        .action((_, o) => o.copy(license = true))
        .text(wrap("Show license agreement for using this software.")),
      opt[Unit](LaunchFlagName)
        .action((_, o) => o.copy(launch = true))
        .text(wrap("Use present JVM instead of launching one with a bigger stack.")),

      // Options specified using flags
      opt[Boolean]("debug")
        .action((x, o) => o.copy(debug = Some(x)))
        .text(wrap("Enable/disable debug mode with exhaustive messages.")),
      opt[String]("fallback").action((x, o) => o.copy(fallback = Some(x))),
      opt[String]("jlink")
        .action((x, o) => o.copy(jlink = Some(x)))
        .valueName("path/to/jlinkNativeLib")
        .text(wrap("Path to Mathematica J/Link library directory.")),
      opt[String]("jlinkinterface")
        .validate(it => if (it == "string" || it == "expr") success else failure("must be 'string' or 'expr'"))
        .action((x, o) => o.copy(jlinkinterface = Some(x)))
        .valueName("string|expr")
        .text(wrap(
          """Whether to send Mathematica commands as
            |strings (more robust) or as
            |expr (supports larger queries).
            |Default: string (unless configured in keymaerax.conf)
            |""".stripMargin
        )),
      opt[String]("jlinktcpip")
        .validate(it => if (it == "true" || it == "false") success else failure("must be 'true' or 'false'"))
        .action((x, o) => o.copy(jlinktcpip = Some(x)))
        .valueName("true|false")
        .text(wrap(
          """Whether to connect to Mathematica with
            |process communication or
            |over TCP/IP (more robust).
            |Default: false (unless configured in keymaerax.conf)
            |""".stripMargin
        )),
      opt[Boolean]("lax")
        .action((x, o) => o.copy(lax = Some(x)))
        .text(wrap(
          """true: Use lax mode with more flexible parser, printer, prover.
            |false: Use strict mode with no flexibility in prover.
            |""".stripMargin
        )),
      opt[String]("mathkernel")
        .action((x, o) => o.copy(mathkernel = Some(x)))
        .valueName("MathKernel(.exe)")
        .text(wrap("Path to Mathematica kernel executable.")),
      opt[String]("monitor")
        .action((x, o) => o.copy(monitor = Some(Symbol(x))))
        .valueName("ctrl|model")
        .text(wrap("What kind of monitor to generate with ModelPlex.")),
      opt[String]("open").action((x, o) => o.copy(open = Some(x))),
      opt[String]("parallelqe")
        .validate(it => if (it == "true" || it == "false") success else failure("must be 'true' or 'false'"))
        .action((x, o) => o.copy(parallelqe = Some(x)))
        .valueName("true|false")
        .text(wrap(
          """Whether to attempt multiple QE alternatives in parallel.
            |Default: false (unless configured in keymaerax.conf)
            |""".stripMargin
        )),
      opt[String]("parserClass").action((x, o) => o.copy(parserClass = Some(x))),
      opt[String]("qemethod")
        .validate(it => if (it == "Reduce" || it == "Resolve") success else failure("must be 'Reduce' or 'Resolve'"))
        .action((x, o) => o.copy(qemethod = Some(x)))
        .valueName("Reduce|Resolve")
        .text(wrap(
          """Whether to use
            |Reduce (solves equations and eliminates quantifiers) or
            |Resolve (eliminates quantifiers).
            |Default: Reduce (unless configured in keymaerax.conf)
            |""".stripMargin
        )),
      opt[Unit]("sandbox").action((_, o) => o.copy(sandbox = Some(true))),
      opt[String]("tool")
        .action((x, o) => o.copy(tool = Some(x)))
        .valueName("mathematica|z3")
        .text(wrap("Choose which tool to use for real arithmetic.")),
      opt[String]("z3path")
        .action((x, o) => o.copy(z3Path = Some(x)))
        .valueName("path/to/z3")
        .text(wrap("Path to Z3 executable.")),

      // Core commands
      note(""),
      cmd("setup")
        .action((_, o) => o.copy(command = Some(Command.Setup)))
        .text(wrap("Initialize the configuration and lemma cache.")),
      note(""),
      cmd("prove")
        .action((_, o) => o.copy(command = Some(Command.Prove())))
        .text(wrap("Run prover on given archive of models or proofs."))
        .children(
          arg[String]("<in>")
            .action((x, o) => o.updateCommand[Command.Prove](_.copy(in = x)))
            .text(wrap("Input archive file(s) (either a specific file or a wildcard, e.g. *.kyx).")),
          arg[String]("<out>")
            .optional()
            .action((x, o) => o.updateCommand[Command.Prove](_.copy(out = Some(x))))
            .text(wrap("Output proof file (defaults to input file with .kyp suffix).")),
          opt[String]("pt-out")
            .action((x, o) => o.updateCommand[Command.Prove](_.copy(ptOut = Some(x))))
            .valueName("<file>")
            .text(wrap("Output proof term s-expression into a file.")),
          opt[String]("conjecture")
            .action((x, o) => o.updateCommand[Command.Prove](_.copy(ptOut = Some(x))))
            .valueName("<file>")
            .text(wrap(
              """Conjecture file to replace the model in the input file with
                |(either a specific file or a wildcard, e.g. *.kyx).
                |""".stripMargin
            )),
          opt[String]("tactic")
            .action((x, o) => o.updateCommand[Command.Prove](_.copy(tactic = Some(x))))
            .valueName("<file|tactic>")
            .text(wrap(
              """Either a file containing a tactic, or a parseable tactic.
                |Used to prove the entry/entries in the input or conjecture file.
                |""".stripMargin
            )),
          opt[String]("tactic-name")
            .action((x, o) => o.updateCommand[Command.Prove](_.copy(tacticName = Some(x))))
            .valueName("<name>")
            .text(wrap(
              """Which of the tactics in the input file to use
                |(default: check all, falling back to auto if no tactic is listed).
                |Only used if no tactic is specified.
                |""".stripMargin
            )),
          opt[Long]("timeout")
            .action((x, o) => o.updateCommand[Command.Prove](_.copy(timeout = x)))
            .valueName("<number>")
            .text(wrap("How many seconds to try proving before giving up, forever if 0 or less.")),
          opt[Unit]("verbose")
            .action((_, o) => o.updateCommand[Command.Prove](_.copy(verbose = true)))
            .text(wrap("Print verbose proof information.")),
          opt[String]("statistics")
            .action((x, o) => o.updateCommand[Command.Prove](_.copy(statistics = Some(x))))
            .valueName("<printer>")
            .text(wrap("How to print proof statistics.")),
        ),
      note(""),
      cmd("parse")
        .action((_, o) => o.copy(command = Some(Command.Parse())))
        .text(wrap("Return error code 0 if the given model file parses."))
        .children(
          arg[String]("<in>").action((x, o) => o.updateCommand[Command.Parse](_.copy(in = x))).text(wrap("Input file."))
        ),
      note(""),
      cmd("bparse")
        .action((_, o) => o.copy(command = Some(Command.BParse())))
        .text(wrap("Return error code 0 if given bellerophon tactic file parses."))
        .children(
          arg[String]("<in>")
            .action((x, o) => o.updateCommand[Command.BParse](_.copy(in = x)))
            .text(wrap("Input file."))
        ),
      note(""),
      cmd("convert")
        .action((_, o) => o.copy(command = Some(Command.Convert())))
        .text(wrap("Model and tactic conversions."))
        .children(
          arg[String]("<conversion>")
            .action((x, o) => o.updateCommand[Command.Convert](_.copy(conversion = x)))
            .text(wrap(
              """Conversion to perform.
                |Possible values: stripHints, kyx2mat, kyx2smt, smt2kyx, smt2mat, verboseTactics, verbatimTactics
                |""".stripMargin
            )),
          arg[String]("<in>")
            .action((x, o) => o.updateCommand[Command.Convert](_.copy(in = x)))
            .text(wrap("Input file.")),
          arg[String]("<out>")
            .optional()
            .action((x, o) => o.updateCommand[Command.Convert](_.copy(out = Some(x))))
            .text(wrap("Output file.")),
        ),
      note(""),
      cmd("grade")
        .action((_, o) => o.copy(command = Some(Command.Grade())))
        .children(
          arg[String]("<in>")
            .action((x, o) => o.updateCommand[Command.Grade](_.copy(in = x)))
            .text(wrap("File to grade.")),
          arg[String]("<out>")
            .optional()
            .action((x, o) => o.updateCommand[Command.Grade](_.copy(out = Some(x))))
            .text(wrap("Output directory for answer files.")),
          opt[Unit]("export-answers")
            .action((_, o) => o.updateCommand[Command.Grade](_.copy(exportAnswers = true)))
            .text(wrap("Export answers to text files instead of grading.")),
          opt[Unit]("skip-on-parse-error")
            .action((_, o) => o.updateCommand[Command.Grade](_.copy(skipOnParseError = true)))
            .text(wrap("Skip grading on parse errors.")),
        ),

      // Webui commands
      note(""),
      cmd("codegen")
        .action((_, o) => o.copy(command = Some(Command.Codegen())))
        .text(wrap("Generate executable C code from a model file."))
        .children(
          arg[String]("<in>")
            .action((x, o) => o.updateCommand[Command.Codegen](_.copy(in = x)))
            .text(wrap("Input archive file, can be of the form file.kyx#entry.")),
          arg[String]("<out>")
            .optional()
            .action((x, o) => o.updateCommand[Command.Codegen](_.copy(out = Some(x))))
            .text(wrap("Output file (default: input file name with .c suffix).")),
          opt[Unit]("quantitative")
            .action((_, o) => o.updateCommand[Command.Codegen](_.copy(quantitative = true)))
            .text(wrap("Generate a quantitative instead of a boolean monitor.")),
          opt[Boolean]("interval")
            .action((x, o) => o.updateCommand[Command.Codegen](_.copy(interval = x)))
            .valueName("<bool>")
            .text(wrap(
              """true: Guard reals by interval arithmetic in floating point (recommended).
                |false: Skip interval arithmetic presuming no floating point errors.
                |""".stripMargin
            )),
          opt[Seq[String]]("vars")
            .action((x, o) => o.updateCommand[Command.Codegen](_.copy(vars = Some(x))))
            .valueName("<vars>")
            .text(wrap("Use ordered comma-separated list of variables, treating others as constant functions.")),
        ),
      note(""),
      cmd("modelplex")
        .action((_, o) => o.copy(command = Some(Command.Modelplex())))
        .text(wrap("Synthesize a monitor from a model by proof with the ModelPlex tactic."))
        .children(
          arg[String]("<in>")
            .action((x, o) => o.updateCommand[Command.Modelplex](_.copy(in = x)))
            .text(wrap("Input file.")),
          arg[String]("<out>")
            .optional()
            .action((x, o) => o.updateCommand[Command.Modelplex](_.copy(out = Some(x))))
            .text(wrap("Output file.")),
          opt[String]("pt-out")
            .action((x, o) => o.updateCommand[Command.Modelplex](_.copy(ptOut = Some(x))))
            .valueName("<file>"),
          opt[Seq[String]]("vars")
            .action((x, o) => o.updateCommand[Command.Modelplex](_.copy(vars = Some(x))))
            .valueName("<vars>")
            .text(wrap("Use ordered comma-separated list of variables, treating others as constant functions.")),
          opt[Unit]("verify").action((_, o) => o.updateCommand[Command.Modelplex](_.copy(verify = true))),
        ),
      note(""),
      cmd("repl")
        .action((_, o) => o.copy(command = Some(Command.Repl())))
        .text(wrap("Prove a model interactively from a command line REPL."))
        .children(
          arg[String]("<model>").action((x, o) => o.copy(model = Some(x))),
          arg[String]("<tactic>").optional().action((x, o) => o.updateCommand[Command.Repl](_.copy(tactic = Some(x)))),
          arg[String]("<scaladefs>").optional().action((x, o) => o.copy(scaladefs = Some(x))),
        ),
      note(""),
      cmd("ui").action((_, o) => o.copy(command = Some(Command.Ui))).text(wrap("Start web user interface.")),
    )
  }

  def parseArgs(name: String, args: Seq[String]): Options = {
    val parser = this.parser(name)

    // When parse() returns None, it failed to parse the arguments
    // and will have already printed some sort of error message.
    val options = OParser.parse(parser, args, Options(name = name, args = args)).getOrElse(sys.exit(1))

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
