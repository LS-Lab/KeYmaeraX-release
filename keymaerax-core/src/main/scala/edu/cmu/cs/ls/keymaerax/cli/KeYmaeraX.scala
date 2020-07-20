package edu.cmu.cs.ls.keymaerax.cli

import java.io.PrintWriter
import java.util.concurrent.TimeUnit

import edu.cmu.cs.ls.keymaerax.{Configuration, KeYmaeraXStartup}
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.{FixedGenerator, MathematicaToolProvider, MultiToolProvider, NoneToolProvider, TactixInit, ToolProvider, WolframEngineToolProvider, WolframScriptToolProvider, Z3ToolProvider}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser.{Declaration, ParsedArchiveEntry}
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXArchiveParser, KeYmaeraXArchivePrinter, KeYmaeraXPrettyPrinter}
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool
import edu.cmu.cs.ls.keymaerax.tools.install.{DefaultConfiguration, ToolConfiguration}

import scala.annotation.tailrec
import scala.collection.immutable.Nil
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext, Future}
import scala.reflect.io.File

/** KeYmaera X basic command line interface. */
object KeYmaeraX {

  type OptionMap = Map[Symbol, Any]

  /** Names of actions that KeYmaera X command line interface supports. */
  object Modes {
    val CODEGEN: String = "codegen"
    val MODELPLEX: String = "modelplex"
    val PROVE: String = "prove"
    val REPL: String = "repl"
    val STRIPHINTS: String = "striphints"
    val SETUP: String = "setup"
    val modes: Set[String] = Set(CODEGEN, MODELPLEX, PROVE, REPL, STRIPHINTS, SETUP)
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
    //@note 'commandLine is passed in to preserve evidence of what generated the output.
    val (options, unprocessedArgs) = nextOption(Map('commandLine -> args.mkString(" ")), args.toList, Usage.cliUsage)
    if (unprocessedArgs.nonEmpty) println("WARNING: Unknown arguments " + unprocessedArgs.mkString(" "))
    try {
      runCommand(options, Usage.cliUsage)
    } finally {
      shutdownProver()
    }
  }

  /** Runs the command 'mode in `options` with command options from `options`, prints `usage` on usage error. */
  def runCommand(options: OptionMap, usage: String): Unit = {
    //@todo allow multiple passes by filter architecture: -prove bla.key -tactic bla.scal -modelplex -codegen
    options.get('mode) match {
      case Some(Modes.PROVE) =>
        initializeProver(combineConfigs(options, configFromFile("z3")), usage)
        KeYmaeraXProofChecker.prove(options, usage)
      case Some(Modes.SETUP) =>
        println("Initializing lemma cache...")
        KeYmaeraXStartup.initLemmaCache()
        println("...done")
      case Some(Modes.STRIPHINTS) =>
        initializeProver(combineConfigs(options, configFromFile("z3")), usage)
        stripHints(options, usage)
      case command => println("WARNING: Unknown command " + command)
    }
  }

  /** Initializes the backend solvers, tactic interpreter, and invariant generator. */
  def initializeProver(options: OptionMap, usage: String): Unit = {
    options.getOrElse('tool, "z3") match {
      case Tools.MATHEMATICA => initMathematica(options, usage)
      case Tools.WOLFRAMENGINE => initWolframEngine(options, usage)
      case Tools.WOLFRAMSCRIPT => initWolframScript(options, usage)
      case Tools.Z3 => initZ3(options)
      case tool => throw new Exception("Unknown tool " + tool + "; use one of " + Tools.tools.mkString("|"))
    }

    KeYmaeraXTool.init(Map.empty)

    //@note just in case the user shuts down the prover from the command line
    Runtime.getRuntime.addShutdownHook(new Thread() { override def run(): Unit = { shutdownProver() } })
  }

  /** Shuts down the backend solver and invariant generator. */
  def shutdownProver(): Unit = {
    implicit val ec: ExecutionContext = ExecutionContext.global
    Await.ready(Future { ToolProvider.shutdown() }, Duration(5, TimeUnit.SECONDS))
    ToolProvider.setProvider(new NoneToolProvider())
    TactixInit.invSupplier = FixedGenerator(Nil)
    KeYmaeraXTool.shutdown()
    //@note do not System.exit in here, which causes Runtime shutdown hook to re-enter this method and block
  }

  /** Exit gracefully */
  def exit(status: Int): Nothing = { shutdownProver(); sys.exit(status) }

  /** Fills `options` from `args`, printing `usage` on error.  */
  @tailrec
  def nextOption(options: OptionMap, args: List[String], usage: String): (OptionMap, List[String]) = {
    args match {
      case Nil => (options, args)
      case "-help" :: _ => println(usage); exit(1)
      case "-license" :: _ => println(License.license); exit(1)
      // actions and their options
      case "-bparse" :: value :: _ =>
        initializeProver(options, usage) //@note parsing a tactic requires prover (AxiomInfo)
        if (parseBelleTactic(value)) exit(0) else exit(-1)
      case "-conjecture" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(options ++ Map('conjecture -> value), tail, usage)
        else { Usage.optionErrorReporter("-conjecture", usage); exit(1) }
      case "-parse" :: value :: _ =>
        //@note parsing an archive with tactics requires initialized axiom info (some of which derive with QE)
        initializeProver(options, usage)
        if (parseProblemFile(value)) exit(0) else exit(-1)
      case "-prove" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(options ++ Map('mode -> Modes.PROVE, 'in -> value), tail, usage)
        else { Usage.optionErrorReporter("-prove", usage); exit(1) }
      case "-savept" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(options ++ Map('ptOut -> value), tail, usage)
        else { Usage.optionErrorReporter("-savept", usage); exit(1) }
      case "-setup" :: tail => nextOption(options ++ Map('mode -> Modes.SETUP), tail, usage)
      case "-striphints" :: kyx :: tail =>
        if (kyx.nonEmpty && !kyx.toString.startsWith("-")) nextOption(options ++ Map('mode -> Modes.STRIPHINTS, 'in -> kyx), tail, usage)
        else { Usage.optionErrorReporter("-striphints", usage); exit(1) }
      case "-tactic" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(options ++ Map('tactic -> value), tail, usage)
        else { Usage.optionErrorReporter("-tactic", usage); exit(1) }
      case "-tacticName" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(options ++ Map('tacticName -> value), tail, usage)
        else { Usage.optionErrorReporter("-tacticName", usage); exit(1) }
      case "-tool" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(options ++ Map('tool -> value.toLowerCase), tail, usage)
        else { Usage.optionErrorReporter("-tool", usage); exit(1) }
      case "-verbose" :: tail => nextOption(options ++ Map('verbose -> true), tail, usage)
      // aditional options
      case "-mathkernel" :: value :: tail =>
        if(value.nonEmpty && !value.toString.startsWith("-")) nextOption(options ++ Map('mathkernel -> value), tail, usage)
        else { Usage.optionErrorReporter("-mathkernel", usage); exit(1) }
      case "-jlink" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(options ++ Map('jlink -> value), tail, usage)
        else { Usage.optionErrorReporter("-jlink", usage); exit(1) }
      // global options
      case "-lax" :: tail => Configuration.set(Configuration.Keys.LAX, "true", saveToFile = false); nextOption(options, tail, usage)
      case "-strict" :: tail => Configuration.set(Configuration.Keys.LAX, "false", saveToFile = false); nextOption(options, tail, usage)
      case "-debug" :: tail => Configuration.set(Configuration.Keys.DEBUG, "true", saveToFile = false); nextOption(options, tail, usage)
      case "-nodebug" :: tail => Configuration.set(Configuration.Keys.DEBUG, "false", saveToFile = false); nextOption(options, tail, usage)
      case "-timeout" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(options ++ Map('timeout -> value.toLong), tail, usage)
        else { Usage.optionErrorReporter("-timeout", usage); exit(1) }
      case _ => (options, args)
    }
  }

  /** Reads configuration from keymaerax.conf. */
  def configFromFile(defaultTool: String): OptionMap = {
    Configuration.get[String](Configuration.Keys.QE_TOOL).getOrElse(defaultTool).toLowerCase() match {
      case Tools.MATHEMATICA => Map('tool -> Tools.MATHEMATICA) ++
        ToolConfiguration.mathematicaConfig.map({ case (k,v) => Symbol(k) -> v })
      case Tools.WOLFRAMENGINE => Map('tool -> Tools.WOLFRAMENGINE) ++
        ToolConfiguration.wolframEngineConfig.map({ case (k,v) => Symbol(k) -> v })
      case Tools.Z3 => Map('tool -> Tools.Z3) ++ ToolConfiguration.z3Config.map({ case (k, v) => Symbol(k) -> v })
      case t => throw new Exception("Unknown tool '" + t + "'")
    }
  }

  /** Combines tool configurations, favoring primary configuration over secondary configuration. */
  def combineConfigs(primary: OptionMap, secondary: OptionMap): OptionMap = {
    primary ++ secondary.filterKeys(!primary.keySet.contains(_))
  }

  /** Initializes Z3 from command line options. */
  private def initZ3(options: OptionMap): Unit = {
    ToolProvider.setProvider(new Z3ToolProvider())
  }

  /** Initializes Mathematica from command line options, if present; else from default config */
  private def initMathematica(options: OptionMap, usage: String): Unit = {
    ToolProvider.setProvider(new MultiToolProvider(new MathematicaToolProvider(mathematicaConfig(options, usage)) :: new Z3ToolProvider() :: Nil))
  }

  /** Initializes Wolfram Engine from command line options. */
  private def initWolframEngine(options: OptionMap, usage: String): Unit = {
    Configuration.set(Configuration.Keys.MATH_LINK_TCPIP, "true", saveToFile = false)
    ToolProvider.setProvider(new MultiToolProvider(new WolframEngineToolProvider(mathematicaConfig(options, usage)) :: new Z3ToolProvider() :: Nil))
  }

  /** Initializes Wolfram Script from command line options. */
  private def initWolframScript(options: OptionMap, usage: String): Unit = {
    ToolProvider.setProvider(new MultiToolProvider(new WolframScriptToolProvider :: new Z3ToolProvider() :: Nil))
  }

  /** Reads the mathematica configuration from command line options, if specified, otherwise from default configuration.  */
  private def mathematicaConfig(options: OptionMap, usage: String): Map[String, String] = {
    assert((options.contains('mathkernel) && options.contains('jlink)) || (!options.contains('mathkernel) && !options.contains('jlink)),
      "\n[Error] Please always use command line option -mathkernel and -jlink together," +
        "and specify the Mathematica link paths with:\n" +
        " -mathkernel PATH_TO_" + DefaultConfiguration.defaultMathLinkName._1 + "_FILE" +
        " -jlink PATH_TO_DIRECTORY_CONTAINS_" +  DefaultConfiguration.defaultMathLinkName._2 + "_FILE \n\n" + usage)

    val mathematicaConfig =
      if (options.contains('mathkernel) && options.contains('jlink)) Map("linkName" -> options('mathkernel).toString,
        "libDir" -> options('jlink).toString, "tcpip" -> options.getOrElse('tcpip, "true").toString)
      else DefaultConfiguration.defaultMathematicaConfig

    val linkNamePath = mathematicaConfig.get("linkName") match {
      case Some(path) => path
      case _ => ""
    }
    val libDirPath = mathematicaConfig.get("libDir") match {
      case Some(path) => path
      case _ => ""
    }
    assert(linkNamePath!="" && libDirPath!="",
      "\n[Error] The paths to MathKernel file named " + DefaultConfiguration.defaultMathLinkName._1 + " and jlinkLibDir file named " + DefaultConfiguration.defaultMathLinkName._2 + " are not specified! " +
        "(On your system, they could look like: " + {if(DefaultConfiguration.defaultMathLinkPath._1!="") DefaultConfiguration.defaultMathLinkPath._1 else DefaultConfiguration.exemplaryMathLinkPath._1} +
        " and " + {if(DefaultConfiguration.defaultMathLinkPath._2!="") DefaultConfiguration.defaultMathLinkPath._2 else DefaultConfiguration.exemplaryMathLinkPath._2} + ")\n" +
        "Please specify the paths to " + DefaultConfiguration.defaultMathLinkName._1 + " and " + DefaultConfiguration.defaultMathLinkName._2 + " with command line option:" +
        " -mathkernel PATH_TO_" + DefaultConfiguration.defaultMathLinkName._1 + "_FILE" +
        " -jlink PATH_TO_DIRECTORY_CONTAINS_" +  DefaultConfiguration.defaultMathLinkName._2 + "_FILE\n" +
        "[Note] Please always use command line option -mathkernel and -jlink together. \n\n" + usage)
    assert(linkNamePath.endsWith(DefaultConfiguration.defaultMathLinkName._1) && new java.io.File(linkNamePath).exists(),
      "\n[Error] Cannot find MathKernel file named " + DefaultConfiguration.defaultMathLinkName._1 + " in path: " + linkNamePath+ "! " +
        "(On your system, it could look like: " + {if(DefaultConfiguration.defaultMathLinkPath._1!="") DefaultConfiguration.defaultMathLinkPath._1 else DefaultConfiguration.exemplaryMathLinkPath._1} + ")\n" +
        "Please specify the correct path that points to " + DefaultConfiguration.defaultMathLinkName._1 + " file with command line option:" +
        " -mathkernel PATH_TO_" + DefaultConfiguration.defaultMathLinkName._1 + "_FILE\n" +
        "[Note] Please always use command line option -mathkernel and -jlink together. \n\n" + usage)
    assert(new java.io.File(libDirPath + File.separator + DefaultConfiguration.defaultMathLinkName._2).exists(),
      "\n[Error] Cannot find jlinkLibDir file named " + DefaultConfiguration.defaultMathLinkName._2 + " in path " + libDirPath+ "! " +
        "(On your system, it could look like: " + {if(DefaultConfiguration.defaultMathLinkPath._2!="") DefaultConfiguration.defaultMathLinkPath._2 else DefaultConfiguration.exemplaryMathLinkPath._2} + ")\n" +
        "Please specify the correct path that points to the directory contains " + DefaultConfiguration.defaultMathLinkName._2 + " file with command line option:" +
        " -jlink PATH_TO_DIRECTORY_CONTAINS_" +  DefaultConfiguration.defaultMathLinkName._2 + "_FILE\n" +
        "[Note] Please always use command line option -mathkernel and -jlink together. \n\n" + usage)

    mathematicaConfig
  }

  /** Parses the content of file `fileName`. */
  private def parseProblemFile(fileName: String): Boolean = {
    println("Parsing " + fileName + "...")
    try {
      KeYmaeraXArchiveParser.parseFromFile(fileName).foreach(e => {
        println(e.name)
        println(KeYmaeraXPrettyPrinter(e.model))
        println("Parsed file successfully")
      })
      true
    } catch {
      case e: Throwable =>
        if (Configuration(Configuration.Keys.DEBUG)=="true") e.printStackTrace()
        println(e.getMessage)
        println(e.getCause)
        println("Failed to parse file")
        false
    }
  }

  private def parseBelleTactic(fileName: String): Boolean = {
    val source = scala.io.Source.fromFile(fileName, "ISO-8859-1")
    try {
      BelleParser(source.getLines().mkString("\n"))
      println("Parsed file successfully")
      true
    } catch {
      case e: Throwable =>
        if (Configuration(Configuration.Keys.DEBUG)=="true") e.printStackTrace()
        println(e)
        println("Failed to parse file")
        false
    } finally {
      source.close()
    }
  }

  /** Strips proof hints from the model. */
  def stripHints(options: OptionMap, usage: String): Unit = {
    require(options.contains('in) && options.contains('out), usage)

    val kyxFile = options('in).toString
    val archiveContent = KeYmaeraXArchiveParser.parseFromFile(kyxFile)

    //@note remove all tactics, e.model does not contain annotations anyway
    //@note fully expand model and remove all definitions too, those might be used as proof hints
    def stripEntry(e: ParsedArchiveEntry): ParsedArchiveEntry = e.copy(model = e.defs.exhaustiveSubst(e.model),
      defs = Declaration(Map.empty), tactics = Nil, annotations = Nil)

    val printer = new KeYmaeraXArchivePrinter()
    val printedStrippedContent = archiveContent.map(stripEntry).map(printer(_)).mkString("\n\n")

    val outFile = options('out).toString
    val pw = new PrintWriter(outFile)
    pw.write(printedStrippedContent)
    pw.close()
  }

}
