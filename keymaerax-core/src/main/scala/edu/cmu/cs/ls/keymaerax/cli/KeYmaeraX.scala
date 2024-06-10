/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.bellerophon.ProverSetupException
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.{
  FixedGenerator,
  MathematicaToolProvider,
  MultiToolProvider,
  NoneToolProvider,
  TactixInit,
  ToolProvider,
  WolframEngineToolProvider,
  WolframScriptToolProvider,
  Z3ToolProvider,
}
import edu.cmu.cs.ls.keymaerax.core.{Formula, PrettyPrinter, StaticSemantics}
import edu.cmu.cs.ls.keymaerax.info.TechnicalName
import edu.cmu.cs.ls.keymaerax.parser.{
  ArchiveParser,
  Declaration,
  KeYmaeraXArchivePrinter,
  Name,
  ParsedArchiveEntry,
  PrettierPrintFormatProvider,
}
import edu.cmu.cs.ls.keymaerax.tools.ext.SmtLibReader
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration
import edu.cmu.cs.ls.keymaerax.tools.qe.{DefaultSMTConverter, KeYmaeraToMathematica}
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaeraXTool, ToolPathFinder}
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration, KeYmaeraXStartup}

import java.io.{FileReader, PrintWriter}
import java.nio.file.{Files, Paths}
import java.util.concurrent.TimeUnit
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext, Future}

/** KeYmaera X basic command line interface. */
object KeYmaeraX {
  object Conversions {
    val STRIPHINTS: String = "stripHints"
    val KYX2MAT: String = "kyx2mat"
    val KYX2SMT: String = "kyx2smt"
    val SMT2KYX: String = "smt2kyx"
    val SMT2MAT: String = "smt2mat"
    val conversions: Set[String] = Set(STRIPHINTS, KYX2MAT, KYX2SMT, SMT2KYX, SMT2MAT)
  }

  /** Backend tools. */
  object Tools {
    val MATHEMATICA: String = "mathematica"
    val WOLFRAMENGINE: String = "wolframengine"
    val WOLFRAMSCRIPT: String = "wolframscript"
    val Z3: String = "z3"
    val tools: Set[String] = Set(MATHEMATICA, WOLFRAMENGINE, WOLFRAMSCRIPT, Z3)
  }

  def main(args: Array[String]): Unit = {
    val options = Options.parseArgs(s"$TechnicalName-core", args)

    try {
      Configuration.setConfiguration(FileConfiguration)
      initializeConfig(options)
      runCommand(options)
    } finally { shutdownProver() }
  }

  /** Set up values in the global config based on command-line options. */
  def initializeConfig(options: Options): Unit = {
    for (value <- options.parserClass) { Configuration.set(Configuration.Keys.PARSER, value, saveToFile = false) }

    for (value <- options.mathkernel) {
      if (Files.exists(Paths.get(value))) {
        Configuration.set(Configuration.Keys.MATHEMATICA_LINK_NAME, value, saveToFile = false)
      } else {
        println("[Error -mathkernel] Mathematica kernel file does not exist: " + value)
        exit(2)
      }
    }

    for (value <- options.jlink) {
      if (Files.exists(Paths.get(value))) {
        Configuration.set(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR, value, saveToFile = false)
      } else {
        println("[Error -jlink] Path to JLink native library does not exist: " + value)
        exit(2)
      }
    }

    for (value <- options.jlinkinterface) {
      Configuration.set(Configuration.Keys.JLINK_USE_EXPR_INTERFACE, (value == "expr").toString, saveToFile = false)
    }

    for (value <- options.qemethod) {
      Configuration.set(Configuration.Keys.MATHEMATICA_QE_METHOD, value, saveToFile = false)
    }

    for (value <- options.jlinktcpip) {
      Configuration.set(Configuration.Keys.MATH_LINK_TCPIP, value.toString, saveToFile = false)
    }

    for (value <- options.parallelqe) {
      Configuration.set(Configuration.Keys.MATHEMATICA_PARALLEL_QE, value.toString, saveToFile = false)
    }

    for (value <- options.z3Path) {
      if (Files.exists(Paths.get(value))) { Configuration.set(Configuration.Keys.Z3_PATH, value, saveToFile = false) }
      else {
        println("[Error -z3path] Z3 executable does not exist: " + value)
        exit(2)
      }
    }

    for (value <- options.lax) { Configuration.set(Configuration.Keys.LAX, value.toString, saveToFile = false) }

    for (value <- options.debug) { Configuration.set(Configuration.Keys.DEBUG, value.toString, saveToFile = false) }
  }

  /** Runs the command 'mode in `options` with command options from `options`, prints `usage` on usage error. */
  def runCommand(options: Options): Unit = {
    options.command match {
      // Core commands
      case Some(Command.Setup) =>
        println("Initializing lemma cache...")
        initializeBackend(options.toToolConfig)
        KeYmaeraXStartup.initLemmaCache()
        println("...done")
      case Some(cmd: Command.Prove) =>
        initializeProver(combineToolConfigs(options.toToolConfig, toolConfigFromFile("z3")))
        KeYmaeraXProofChecker.prove(
          in = cmd.in,
          out = cmd.out,
          ptOut = cmd.ptOut,
          conjecture = cmd.conjecture,
          tactic = cmd.tactic,
          tacticName = cmd.tacticName,
          timeout = cmd.timeout,
          verbose = cmd.verbose,
          statistics = cmd.statistics,
          args = options.args,
        )
      case Some(cmd: Command.Parse) =>
        // Parsing an archive with tactics requires initialized axiom info (some of which derive with QE)
        initializeProver(options.toToolConfig)
        if (parseProblemFile(cmd.in)) exit(0) else exit(-1)
      case Some(cmd: Command.BParse) =>
        // Parsing a tactic requires prover (AxiomInfo)
        initializeProver(options.toToolConfig)
        if (parseBelleTactic(cmd.in)) exit(0) else exit(-1)
      case Some(cmd: Command.Convert) =>
        initializeProver(combineToolConfigs(options.toToolConfig, toolConfigFromFile("z3")))
        convert(in = cmd.in, out = cmd.out, conversion = cmd.conversion)
      case Some(cmd: Command.Grade) =>
        initializeProver(combineToolConfigs(options.toToolConfig, toolConfigFromFile("z3")))
        AssessmentProver.grade(
          in = cmd.in,
          out = cmd.out,
          exportAnswers = cmd.exportAnswers,
          skipGradingOnParseError = cmd.skipOnParseError,
          msgOut = System.out,
          resultOut = System.out,
        )
      // Unknown or no commands
      case Some(command) => println("WARNING: Unknown command " + command)
      case None => options.printUsageAndExitWithError()
    }
  }

  /** Initializes the backend solvers, tactic interpreter, and invariant generator. */
  def initializeProver(options: ToolConfiguration): Unit = {
    Configuration.setConfiguration(FileConfiguration)

    initializeBackend(options)

    KeYmaeraXTool.init(interpreter = KeYmaeraXTool.InterpreterChoice.LazySequential, initDerivationInfoRegistry = true)

    // @note just in case the user shuts down the prover from the command line
    Runtime
      .getRuntime
      .addShutdownHook(new Thread() {
        override def run(): Unit = { shutdownProver() }
      })
  }

  /** Initializes the backend solvers. */
  def initializeBackend(options: ToolConfiguration): Unit = {
    options.tool.getOrElse("z3") match {
      case Tools.MATHEMATICA => initMathematica(options)
      case Tools.WOLFRAMENGINE => initWolframEngine(options)
      case Tools.WOLFRAMSCRIPT => initWolframScript(options)
      case Tools.Z3 => initZ3(options)
      case tool => throw new Exception("Unknown tool " + tool + "; use one of " + Tools.tools.mkString("|"))
    }
  }

  /** Shuts down the backend solver and invariant generator. */
  def shutdownProver(): Unit = {
    implicit val ec: ExecutionContext = ExecutionContext.global
    Await.ready(Future { ToolProvider.shutdown() }, Duration(5, TimeUnit.SECONDS))
    ToolProvider.setProvider(new NoneToolProvider())
    TactixInit.invSupplier = FixedGenerator(Nil)
    KeYmaeraXTool.shutdown()
    // @note do not System.exit in here, which causes Runtime shutdown hook to re-enter this method and block
  }

  /** Exit gracefully */
  def exit(status: Int): Nothing = { shutdownProver(); sys.exit(status) }

  /** Reads configuration from keymaerax.conf. */
  def toolConfigFromFile(defaultTool: String): ToolConfiguration = {
    ToolConfiguration.config(Configuration.getString(Configuration.Keys.QE_TOOL).getOrElse(defaultTool))
  }

  /** Combines tool configurations, favoring primary configuration over secondary configuration. */
  def combineToolConfigs(primary: ToolConfiguration, secondary: ToolConfiguration): ToolConfiguration =
    ToolConfiguration(
      tool = primary.tool.orElse(secondary.tool),
      mathKernel = primary.mathKernel.orElse(secondary.mathKernel),
      jlinkLibDir = primary.jlinkLibDir.orElse(secondary.jlinkLibDir),
      tcpip = primary.tcpip.orElse(secondary.tcpip),
      z3Path = primary.z3Path.orElse(secondary.z3Path),
    )

  /** Initializes Z3 from command line options. */
  private def initZ3(options: ToolConfiguration): Unit = {
    ToolProvider.setProvider(Z3ToolProvider())
    if (!ToolProvider.isInitialized)
      throw new ProverSetupException("Failed to initialize Z3; please check the configured path")
  }

  /** Initializes Mathematica from command line options, if present; else from default config */
  private def initMathematica(options: ToolConfiguration): Unit = {
    ToolProvider
      .setProvider(MultiToolProvider(MathematicaToolProvider(mathematicaConfig(options)) :: Z3ToolProvider() :: Nil))
    if (!ToolProvider.isInitialized)
      throw new ProverSetupException("Failed to initialize Mathematica; the license may be expired")
  }

  /** Initializes Wolfram Engine from command line options. */
  private def initWolframEngine(options: ToolConfiguration): Unit = {
    Configuration.set(Configuration.Keys.MATH_LINK_TCPIP, "true", saveToFile = false)
    ToolProvider
      .setProvider(MultiToolProvider(WolframEngineToolProvider(mathematicaConfig(options)) :: Z3ToolProvider() :: Nil))
    if (!ToolProvider.isInitialized) throw new ProverSetupException(
      "Failed to initialize Wolfram Engine; the license may be expired (try starting Wolfram Engine from the command line to renew the license)"
    )
  }

  /** Initializes Wolfram Script from command line options. */
  private def initWolframScript(options: ToolConfiguration): Unit = {
    ToolProvider
      .setProvider(MultiToolProvider(WolframScriptToolProvider(mathematicaConfig(options)) :: Z3ToolProvider() :: Nil))
    if (!ToolProvider.isInitialized) throw new ProverSetupException(
      "Failed to initialize Wolfram Script; the license may be expired (try starting Wolfram Script from the command line to renew the license)"
    )
  }

  /**
   * Reads the mathematica configuration from command line options, if specified, otherwise from default configuration.
   */
  private def mathematicaConfig(options: ToolConfiguration): ToolConfiguration = {
    assert(
      options.mathKernel.isDefined == options.jlinkLibDir.isDefined,
      "[Error] Please always use the command line options -mathkernel and -jlink together.",
    )

    val mathematicaConfig =
      if (options.mathKernel.isDefined && options.jlinkLibDir.isDefined) {
        options.copy(tcpip = options.tcpip.orElse(Some("true")))
      } else ToolConfiguration.defaultMathematicaConfig

    val linkNamePath = mathematicaConfig.mathKernel.getOrElse("")
    val libDirPath = mathematicaConfig.jlinkLibDir.getOrElse("")
    assert(
      linkNamePath != "" && libDirPath != "",
      """[Error] Could not locate math kernel and jlink library.
        |Please specify them using the -mathkernel and -jlink command line options.""".stripMargin,
    )
    assert(
      Files.exists(Paths.get(linkNamePath)),
      s"""[Error] Can't find math kernel at this path:
         |$linkNamePath
         |Please specify the correct path using the -mathkernel command line option.""".stripMargin,
    )
    assert(
      Files.exists(Paths.get(libDirPath).resolve(ToolPathFinder.jlinkLibFileName)),
      s"""[Error] Can't find jlink library in this directory:
         |$libDirPath
         |Please specify the correct path using the -jlink command line option.""".stripMargin,
    )

    mathematicaConfig
  }

  /** Parses the content of file `fileName`. */
  private def parseProblemFile(fileName: String): Boolean = {
    println("Parsing " + fileName + "...")
    try {
      ArchiveParser
        .parseFromFile(fileName)
        .foreach(e => {
          println(e.name)
          println(PrettyPrinter(e.model))
          println("Parsed file successfully")
        })
      true
    } catch {
      case e: Throwable =>
        if (Configuration(Configuration.Keys.DEBUG) == "true") e.printStackTrace()
        println(e.getMessage)
        println(e.getCause)
        println("Failed to parse file")
        false
    }
  }

  private def parseBelleTactic(fileName: String): Boolean = {
    val source = scala.io.Source.fromFile(fileName, edu.cmu.cs.ls.keymaerax.core.ENCODING)
    try {
      BelleParser(source.getLines().mkString("\n"))
      println("Parsed file successfully")
      true
    } catch {
      case e: Throwable =>
        if (Configuration(Configuration.Keys.DEBUG) == "true") e.printStackTrace()
        println(e)
        println("Failed to parse file")
        false
    } finally { source.close() }
  }

  /** Converts input files. */
  def convert(in: String, out: Option[String], conversion: String): Unit = {

    conversion match {
      case Conversions.STRIPHINTS => stripHints(in, out)
      case Conversions.KYX2SMT => kyx2smt(in, out)
      case Conversions.KYX2MAT => kyx2mat(in, out)
      case Conversions.SMT2KYX => smt2kyx(in, out)
      case Conversions.SMT2MAT => smt2mat(in, out)
      case _ => Usage.optionErrorReporter("-convert"); exit(1)
    }
  }

  /** Strips proof hints from the model. */
  private def stripHints(in: String, out: Option[String]): Unit = {
    val converter = (kyxFile: String) => {
      val archiveContent = ArchiveParser.parseFromFile(kyxFile)

      // @note remove all tactics, e.model does not contain annotations anyway
      // @note fully expand model and remove all definitions too, those might be used as proof hints
      def stripEntry(e: ParsedArchiveEntry): ParsedArchiveEntry = {
        val expandedModel = e.defs.exhaustiveSubst(e.model)
        val expandedModelNames = StaticSemantics.symbols(expandedModel)
        e.copy(
          model = expandedModel,
          defs = Declaration(
            e.defs
              .decls
              .flatMap({ case (name @ Name(n, i), sig) =>
                if (expandedModelNames.exists(ns => ns.name == n && ns.index == i))
                  Some(name, sig.copy(interpretation = Right(None)))
                else None
              })
          ),
          tactics = Nil,
          annotations = Nil,
        )
      }

      val printer = new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80))
      archiveContent.map(stripEntry).map(printer(_)).mkString("\n\n")
    }

    convert(in, out, converter)
  }

  /** Converts KeYmaera X to SMT-Lib format. */
  private def kyx2smt(in: String, out: Option[String]): Unit = {
    val converter = (fileName: String) => {
      val archiveContent = ArchiveParser.parseFromFile(fileName)
      archiveContent
        .map(_.model match {
          case fml: Formula =>
            val (decls, expr) = DefaultSMTConverter.generateSMT(fml)
            decls + expr
          case e => throw new IllegalArgumentException("Expected a formula, but got " + e)
        })
        .mkString("\n")
    }
    convert(in, out, converter)
  }

  /** Converts KeYmaera X to Mathematica. */
  private def kyx2mat(in: String, out: Option[String]): Unit = {
    val converter = (fileName: String) => {
      val archiveContent = ArchiveParser.parseFromFile(fileName)
      archiveContent
        .map(_.model match {
          case fml: Formula => KeYmaeraToMathematica(fml)
          case e => throw new IllegalArgumentException("Expected a formula, but got " + e)
        })
        .mkString("\n")
    }
    convert(in, out, converter)
  }

  /** Converts SMT-Lib format to KeYmaera X. */
  private def smt2kyx(in: String, out: Option[String]): Unit = {
    val converter =
      (fileName: String) => { SmtLibReader.read(new FileReader(fileName))._1.map(_.prettyString).mkString("\n") }
    convert(in, out, converter)
  }

  /** Converts SMT-Lib format to Mathematica. */
  private def smt2mat(in: String, out: Option[String]): Unit = {
    val converter = (fileName: String) => {
      val (kyx, _) = SmtLibReader.read(new FileReader(fileName))
      kyx.map(KeYmaeraToMathematica).mkString("\n")
    }
    convert(in, out, converter)
  }

  /** Converts the content of a file using the `converter` fileName => content. */
  private def convert(in: String, out: Option[String], converter: String => String): Unit = {
    val converted = converter(in)
    out match {
      case Some(outFile) =>
        val pw = new PrintWriter(outFile)
        pw.write(converted)
        pw.close()
      case None => println(converted)
    }
  }

}
