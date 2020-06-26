/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.launcher

import java.io.{FilePermission, PrintWriter}
import java.lang.reflect.ReflectPermission
import java.net.URLEncoder
import java.nio.file.attribute.BasicFileAttributes
import java.nio.file.{FileSystems, FileVisitResult, Files, Path, Paths, SimpleFileVisitor}
import java.security.Permission
import java.util.concurrent.TimeUnit

import edu.cmu.cs.ls.keymaerax.{Configuration, KeYmaeraXStartup, StringToVersion}
import edu.cmu.cs.ls.keymaerax.scalatactic.ScalaTacticCompiler
import edu.cmu.cs.ls.keymaerax.bellerophon.IOListeners.PrintProgressListener
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.{BelleParser, BellePrettyPrinter}
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.GenProduct
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser._
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaeraXTool, ToolEvidence}
import edu.cmu.cs.ls.keymaerax.codegen.{CGenerator, CMonitorGenerator}
import edu.cmu.cs.ls.keymaerax.hydra.TempDBTools
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser.{Declaration, ParsedArchiveEntry}
import edu.cmu.cs.ls.keymaerax.pt.{HOLConverter, IsabelleConverter, ProvableSig, TermProvable}

import scala.collection.immutable
import scala.compat.Platform
import scala.util.Random
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tools.install.{DefaultConfiguration, ToolConfiguration}
import org.apache.logging.log4j.MarkerManager
import org.apache.logging.log4j.scala.Logger

import scala.collection.immutable.{List, Nil}
import scala.collection.mutable.ListBuffer
import scala.concurrent.{Await, ExecutionContext, Future, TimeoutException}
import scala.concurrent.duration.Duration
import scala.reflect.io.File
import resource._

import scala.annotation.tailrec

/**
  * Command-line interface launcher for [[http://keymaeraX.org/ KeYmaera X]],
  * the aXiomatic Tactical Theorem Prover for Hybrid Systems and Hybrid Games.
  *
  * - `[[edu.cmu.cs.ls.keymaerax.core]]` - KeYmaera X kernel, proof certificates, main data structures
  * - `[[edu.cmu.cs.ls.keymaerax.btactics]]` - Tactic language library
  * - `[[edu.cmu.cs.ls.keymaerax.bellerophon]]` - Bellerophon tactic language and tactic interpreter
  *
  * @author Stefan Mitsch
  * @author Andre Platzer
  * @author Ran Ji
  * @author Brandon Bohrer
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  * @see Andre Platzer. [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. [[http://arxiv.org/pdf/1503.01981.pdf arXiv 1503.01981]]
  * @see Andre Platzer. [[https://doi.org/10.1007/978-3-319-63588-0 Logical Foundations of Cyber-Physical Systems]]. Springer, 2018.
  * @see Nathan Fulton, Stefan Mitsch, Jan-David Quesel, Marcus Volp and Andre Platzer. [[https://doi.org/10.1007/978-3-319-21401-6_36 KeYmaera X: An axiomatic tactical theorem prover for hybrid systems]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
  * @see Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
  * @see Andre Platzer. [[https://doi.org/10.1109/LICS.2012.13 Logics of dynamical systems]]. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 13-24. IEEE 2012
  * @see [[edu.cmu.cs.ls.keymaerax.launcher.Main]]
  */
object KeYmaeraX {

  private type OptionMap = Map[Symbol, Any]

  /**
    * Names of actions that KeYmaera X command line interface supports.
    */
  object Modes {
    val CODEGEN: String = "codegen"
    val MODELPLEX: String = "modelplex"
    val PROVE: String = "prove"
    val REPL: String = "repl"
    val STRIPHINTS: String = "striphints"
    val UI: String = "ui"
    val SETUP: String = "setup"
    val modes: Set[String] = Set(CODEGEN, MODELPLEX, PROVE, REPL, STRIPHINTS, UI, SETUP)
  }

  /**
    * Names of tools that KeYmaera X command line interface supports in `-tool`.
    */
  object Tools {
    val MATHEMATICA: String = "mathematica"
    val WOLFRAMENGINE: String = "wolframengine"
    val WOLFRAMSCRIPT: String = "wolframscript"
    val Z3: String = "z3"
    val tools: Set[String] = Set(MATHEMATICA, WOLFRAMENGINE, WOLFRAMSCRIPT, Z3)
  }

  /** Usage -help information.
    * @note Formatted to 80 characters terminal width. */
  val usage: String =
    """Usage: java -jar keymaerax.jar
      |  -ui [web server options] |
      |  -prove file.kyx [-conjecture file2.kyx] [-out file.kyp]
      |     [-timeout seconds] [-verbose] |
      |  -modelplex file.kyx [-monitor ctrl|model] [-out file.kym] [-isar]
      |     [-sandbox] [-fallback prg] |
      |  -codegen file.kyx [-vars var1,var2,..,varn] [-out file.c]
      |     [-quantitative ctrl|model|plant] |
      |  -striphints file.kyx -out fileout.kyx
      |  -setup
      |
      |Actions:
      |  -ui        start web user interface with optional server arguments (default)
      |  -prove     run prover on given archive of models or proofs
      |  -modelplex synthesize monitor from given model by proof with ModelPlex tactic
      |  -codegen   generate executable C code from given model file
      |  -striphints remove all proof annotations from the model
      |  -parse     return error code 0 if the given model file parses
      |  -bparse    return error code 0 if given bellerophon tactic file parses
      |  -repl      prove given model interactively from REPL command line
      |  -setup     initializes the configuration and lemma cache
      |
      |Additional options:
      |  -tool mathematica|z3 choose which tool to use for real arithmetic
      |  -mathkernel MathKernel(.exe) path to Mathematica kernel executable
      |  -jlink path/to/jlinkNativeLib path to Mathematica J/Link library directory
      |  -timeout  how many seconds to try proving before giving up, forever if <=0
      |  -monitor  ctrl|model what kind of monitor to generate with ModelPlex
      |  -vars     use ordered list of variables, treating others as constant functions
      |  -interval guard reals by interval arithmetic in floating point (recommended)
      |  -nointerval skip interval arithmetic presuming no floating point errors
      |  -savept path export proof term s-expression from -prove to given path
      |  -launch   use present JVM instead of launching one with a bigger stack
      |  -lax      use lax mode with more flexible parser, printer, prover etc.
      |  -strict   use strict mode with no flexibility in prover
      |  -debug    use debug mode with exhaustive messages
      |  -nodebug  disable debug mode to suppress intermediate messages
      |  -security use security manager imposing some runtime security restrictions
      |  -help     Display this usage information
      |  -license  Show license agreement for using this software
      |
      |Copyright (c) Carnegie Mellon University.
      |Use option -license to show the license conditions.""".stripMargin


  private def launched(): Unit = {
    LAUNCH = true
    //println("Launching KeYmaera X")
  }
  var LAUNCH: Boolean = false

  /** main function to start KeYmaera X from command line. Other entry points exist but this one is best for command line interfaces. */
  def main(args: Array[String]): Unit = {
    if (args.length > 0 && List("-help", "--help", "-h", "-?").contains(args(0))) {
      println(help)
      exit(1)
    }
    println("KeYmaera X Prover" + " " + VERSION + "\n" + "Use option -help for usage and license information")
    if (args.length == 0) launchUI(args)
    else {
      //@note 'commandLine is only passed in to preserve evidence of what generated the output.
      val options = nextOption(Map('commandLine -> args.mkString(" ")), args.toList)

      if(!options.contains('mode)) {
        //@note this should be a bad state but apparently it happens.
        launchUI(args)
      } else if (options.get('mode).contains(Modes.CODEGEN)) {
        //@note Mathematica needed for quantitative ModelPlex
        if (options.get('quantitative).isDefined) {
          initializeProver(combineToolConfigs(options, configFromFile(Tools.MATHEMATICA)))
        }
        codegen(options)
      } else if (!options.get('mode).contains(Modes.UI) ) {
        try {
          initializeProver(combineToolConfigs(options, configFromFile("z3")))

          //@todo allow multiple passes by filter architecture: -prove bla.key -tactic bla.scal -modelplex -codegen
          options.get('mode) match {
            case Some(Modes.PROVE) => prove(options)
            case Some(Modes.MODELPLEX) => modelplex(options)
            case Some(Modes.CODEGEN) => codegen(options)
            case Some(Modes.REPL) => repl(options)
            case Some(Modes.STRIPHINTS) => stripHints(options)
            case Some(Modes.SETUP) =>
              println("Initializing lemma cache...")
              KeYmaeraXStartup.initLemmaCache()
              println("...done")
            case Some(Modes.UI) => assert(false, "already handled above since no prover needed"); ???
          }
        } finally {
          shutdownProver()
        }
      }
    }
  }

  /** Combines tool configurations, favoring command line configuration over file configuration. */
  private def combineToolConfigs(cmdLineConfig: OptionMap, fileConfig: OptionMap): OptionMap = {
    cmdLineConfig ++ fileConfig.filterKeys(!cmdLineConfig.keySet.contains(_))
  }

  /**
    * Statistics about size of prover kernel.
    */
  def stats: String = {
    "    with " + Provable.rules.size + " axiomatic rules and " + Provable.axiom.size + " axioms"
  }

  /**
    * KeYmaera X -help string.
    */
  def help: String = {
    stats + "\n" + usage
  }



  private def configFromFile(defaultTool: String): OptionMap = {
    Configuration.getOption(Configuration.Keys.QE_TOOL).getOrElse(defaultTool).toLowerCase() match {
      case Tools.MATHEMATICA => Map('tool -> Tools.MATHEMATICA) ++
        ToolConfiguration.mathematicaConfig.map({ case (k,v) => Symbol(k) -> v })
      case Tools.WOLFRAMENGINE => Map('tool -> Tools.WOLFRAMENGINE) ++
        ToolConfiguration.wolframEngineConfig.map({ case (k,v) => Symbol(k) -> v })
      case Tools.Z3 => Map('tool -> Tools.Z3) ++ ToolConfiguration.z3Config.map({ case (k, v) => Symbol(k) -> v })
      case t => throw new Exception("Unknown tool '" + t + "'")
    }
  }

  private def makeVariables(varNames: Array[String]): Array[BaseVariable] = {
    varNames.map(vn => KeYmaeraXParser(vn) match {
      case v: BaseVariable => v
      case v => throw new IllegalArgumentException("String " + v + " is not a valid variable name")
    })
  }

  @tailrec
  private def nextOption(map: OptionMap, list: List[String]): OptionMap = {
    list match {
      case Nil => map
      case "-help" :: _ => println(usage); exit(1)
      case "-license" :: _ => println(license); exit(1)
      // actions
      case "-parse" :: value :: tail =>
        parseProblemFile(value); ???
      case "-bparse" :: value :: tail =>
        parseBelleTactic(value); ???
      case "-prove" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('mode -> Modes.PROVE, 'in -> value), tail)
        else optionErrorReporter("-prove")
      case "-verbose" :: tail =>
        require(!map.contains('verbose)); nextOption(map ++ Map('verbose -> true), tail)
      case "-savept" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('ptOut -> value), tail)
        else optionErrorReporter("-savept")
      case "-sandbox" :: tail =>
        nextOption(map ++ Map('sandbox -> true), tail)
      case "-modelplex" :: value :: tail =>
        if(value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('mode -> Modes.MODELPLEX, 'in -> value), tail)
        else optionErrorReporter("-modelPlex")
      case "-isar" :: tail => nextOption(map ++ Map('isar -> true), tail)
      case "-codegen" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('mode -> Modes.CODEGEN, 'in -> value), tail)
        else optionErrorReporter("-codegen")
      case "-quantitative" :: value :: tail => nextOption(map ++ Map('quantitative -> value), tail)
      case "-repl" :: model :: tactic_and_scala_and_tail =>
        val posArgs = tactic_and_scala_and_tail.takeWhile(x => !x.startsWith("-"))
        val restArgs = tactic_and_scala_and_tail.dropWhile(x => !x.startsWith("-"))
        val newMap = List('tactic, 'scaladefs).zip(posArgs).foldLeft(map){case (acc,(k,v)) => acc ++ Map(k -> v)}
        if (model.nonEmpty  && !model.toString.startsWith("-"))
          nextOption(newMap ++ Map('mode -> Modes.REPL, 'model -> model), restArgs)
        else optionErrorReporter("-repl")
      case "-striphints" :: kyx :: tail =>
        if (kyx.nonEmpty && !kyx.toString.startsWith("-")) nextOption(map ++ Map('mode -> Modes.STRIPHINTS, 'in -> kyx), tail)
        else optionErrorReporter("-striphints")
      case "-setup" :: tail => nextOption(map ++ Map('mode -> Modes.SETUP), tail)
      case "-ui" :: tail => launchUI(tail.toArray); map ++ Map('mode -> Modes.UI)
      // action options
      case "-out" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('out -> value), tail)
        else optionErrorReporter("-out")
      case "-conjecture" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('conjecture -> value), tail)
        else optionErrorReporter("-conjecture")
      case "-fallback" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('fallback -> value), tail)
        else optionErrorReporter("-fallback")
      case "-vars" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('vars -> makeVariables(value.split(","))), tail)
        else optionErrorReporter("-vars")
      case "-monitor" :: value :: tail =>
        if(value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('monitor -> Symbol(value)), tail)
        else optionErrorReporter("-monitor")
      case "-tactic" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('tactic -> value), tail)
        else optionErrorReporter("-tactic")
      case "-tacticName" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('tacticName -> value), tail)
        else optionErrorReporter("-tacticName")
      case "-interactive" :: tail => nextOption(map ++ Map('interactive -> true), tail)
      case "-tool" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('tool -> value.toLowerCase), tail)
        else optionErrorReporter("-tool")
      // aditional options
      case "-mathkernel" :: value :: tail =>
        if(value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('mathkernel -> value), tail)
        else optionErrorReporter("-mathkernel")
      case "-jlink" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('jlink -> value), tail)
        else optionErrorReporter("-jlink")
      case "-interval" :: tail => require(!map.contains('interval)); nextOption(map ++ Map('interval -> true), tail)
      case "-nointerval" :: tail => require(!map.contains('interval)); nextOption(map ++ Map('interval -> false), tail)
      case "-dnf" :: tail => require(!map.contains('dnf)); nextOption(map ++ Map('dnf -> true), tail)
      // global options
      case "-lax" :: tail => Configuration.set(Configuration.Keys.LAX, "true", saveToFile = false); nextOption(map, tail)
      case "-strict" :: tail => Configuration.set(Configuration.Keys.LAX, "false", saveToFile = false); nextOption(map, tail)
      case "-debug" :: tail => Configuration.set(Configuration.Keys.DEBUG, "true", saveToFile = false); nextOption(map, tail)
      case "-nodebug" :: tail => Configuration.set(Configuration.Keys.DEBUG, "false", saveToFile = false); nextOption(map, tail)
      case "-security" :: tail => activateSecurity(); nextOption(map, tail)
      case "-launch" :: tail => launched(); nextOption(map, tail)
      case "-timeout" :: value :: tail =>
        if (value.nonEmpty && !value.toString.startsWith("-")) nextOption(map ++ Map('timeout -> value.toLong), tail)
        else optionErrorReporter("-timeout")
      case option :: tail => optionErrorReporter(option)
    }
  }

  private def parseProblemFile(fileName: String) = {
    try {
      initializeProver(Map('tool -> "z3")) //@note parsing an archive with tactics requires prover (AxiomInfo)
      KeYmaeraXArchiveParser.parseFromFile(fileName).foreach(e => {
        println(e.name)
        println(KeYmaeraXPrettyPrinter(e.model))
        println("Parsed file successfully")
      })
      sys.exit(0)
    } catch {
      case e: Throwable =>
        if (Configuration(Configuration.Keys.DEBUG)=="true") e.printStackTrace()
        println(e.getMessage)
        println(e.getCause)
        println("Failed to parse file")
        sys.exit(-1)
    }
  }

  private def parseBelleTactic(fileName: String) = {
    try {
      initializeProver(Map('tool -> "z3")) //@note parsing a tactic requires prover (AxiomInfo)
      val fileContents: String = managed(scala.io.Source.fromFile(fileName, "ISO-8859-1")).apply(_.getLines().mkString("\n"))
      BelleParser(fileContents)
      println("Parsed file successfully")
      sys.exit(0)
    } catch {
      case e: Throwable =>
        if (Configuration(Configuration.Keys.DEBUG)=="true") e.printStackTrace()
        println(e)
        println("Failed to parse file")
        sys.exit(-1)
    }
  }

  /** Prints help messages for command line options. */
  private def optionErrorReporter(option: String) = {
    val noValueMessage = "[Error] No value specified for " + option + " option. "
    option match {
      case "-prove" => println(noValueMessage + "Please use: -prove FILENAME.[key/kyx]\n\n" + usage); exit(1)
      case "-modelPlex" => println(noValueMessage + "Please use: -modelPlex FILENAME.[key/kyx]\n\n" + usage); exit(1)
      case "-codegen" => println(noValueMessage + "Please use: -codegen FILENAME.kym\n\n" + usage); exit(1)
      case "-out" => println(noValueMessage + "Please use: -out FILENAME.proof | FILENAME.kym | FILENAME.c | FILENAME.g\n\n" + usage); exit(1)
      case "-conjecture" => println(noValueMessage + "Please use: -conjecture FILENAME.kyx\n\n" + usage); exit(1)
      case "-vars" => println(noValueMessage + "Please use: -vars VARIABLE_1,VARIABLE_2,...\n\n" + usage); exit(1)
      case "-tactic" =>  println(noValueMessage + "Please use: -tactic FILENAME.[scala|kyt]\n\n" + usage); exit(1)
      case "-mathkernel" => println(noValueMessage + "Please use: -mathkernel PATH_TO_" + DefaultConfiguration.defaultMathLinkName._1 + "_FILE\n\n" + usage); exit(1)
      case "-jlink" => println(noValueMessage + "Please use: -jlink PATH_TO_DIRECTORY_CONTAINS_" +  DefaultConfiguration.defaultMathLinkName._2 + "_FILE\n\n" + usage); exit(1)
      case "-tool" => println(noValueMessage + "Please use: -tool mathematica|wolframengine|z3\n\n" + usage); exit(1)
      case _ =>  println("[Error] Unknown option " + option + "\n\n" + usage); exit(1)
    }
  }

  /** Initializes the backend solvers, tactic interpreter, and invariant generator. */
  private def initializeProver(options: OptionMap): Unit = {
    options('tool) match {
      case Tools.MATHEMATICA => initMathematica(options)
      case Tools.WOLFRAMENGINE => initWolframEngine(options)
      case Tools.WOLFRAMSCRIPT => initWolframScript(options)
      case Tools.Z3 => initZ3(options)
      case tool => throw new Exception("Unknown tool " + tool + "; use one of " + Tools.tools.mkString("|"))
    }

    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    BelleInterpreter.setInterpreter(LazySequentialInterpreter())
    DerivationInfoRegistry.init
    Ax.prepopulateDerivedLemmaDatabase()
    KeYmaeraXTool.init(Map.empty)

    val generator = new ConfigurableGenerator[GenProduct]()
    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) =>
      generator.products += (p->(generator.products.getOrElse(p, Nil) :+ (inv, None))))
    TactixLibrary.invSupplier = generator

    //@note just in case the user shuts down the prover from the command line
    Runtime.getRuntime.addShutdownHook(new Thread() { override def run(): Unit = { shutdownProver() } })
  }

  /** Initializes Z3 from command line options. */
  private def initZ3(options: OptionMap): Unit = {
    ToolProvider.setProvider(new Z3ToolProvider())
  }

  private def mathematicaConfig(options: OptionMap): Map[String, String] = {
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

  /** Initializes Mathematica from command line options, if present; else from default config */
  private def initMathematica(options: OptionMap): Unit = {
    ToolProvider.setProvider(new MultiToolProvider(new MathematicaToolProvider(mathematicaConfig(options)) :: new Z3ToolProvider() :: Nil))
  }

  /** Initializes Wolfram Engine from command line options. */
  private def initWolframEngine(options: OptionMap): Unit = {
    Configuration.set(Configuration.Keys.MATH_LINK_TCPIP, "true", saveToFile = false)
    ToolProvider.setProvider(new MultiToolProvider(new WolframEngineToolProvider(mathematicaConfig(options)) :: new Z3ToolProvider() :: Nil))
  }

  /** Initializes Wolfram Script from command line options. */
  private def initWolframScript(options: OptionMap): Unit = {
    ToolProvider.setProvider(new MultiToolProvider(new WolframScriptToolProvider :: new Z3ToolProvider() :: Nil))
  }

  /** Shuts down the backend solver and invariant generator. */
  private def shutdownProver(): Unit = {
    implicit val ec: ExecutionContext = ExecutionContext.global
    Await.ready(Future { ToolProvider.shutdown() }, Duration(5, TimeUnit.SECONDS))
    ToolProvider.setProvider(new NoneToolProvider())
    TactixLibrary.invSupplier = FixedGenerator(Nil)
    KeYmaeraXTool.shutdown()
    //@note do not System.exit in here, which causes Runtime shutdown hook to re-enter this method and block
  }

  /** Exit gracefully */
  private def exit(status: Int): Nothing = {shutdownProver(); sys.exit(status)}

  /** Generate a header stamping the source of a generated file */
  //@todo Of course this has a security attack for non-letter characters like end of comments from command line
  private def stampHead(options: OptionMap): String = "/* @evidence: generated by KeYmaeraX " + VERSION + " " + nocomment(options.getOrElse('commandLine, "<unavailable>").asInstanceOf[String]) + " */\n\n"

  /** Replace C-style line-comments in command line (from wildcard paths) */
  private def nocomment(s: String): String = s.replaceAllLiterally("/*", "/STAR").replaceAllLiterally("*/", "STAR/")

  /** Reads the value of 'tactic from the `options` (either a file name or a tactic expression).
    * Default [[TactixLibrary.auto]] if `options` does not contain 'tactic. */
  private def readTactic(options: OptionMap, defs: Declaration): Option[BelleExpr] = {
    options.get('tactic) match {
      case Some(t) if File(t.toString).exists =>
        val fileName = t.toString
        val source = managed(scala.io.Source.fromFile(fileName, "ISO-8859-1")).apply(_.mkString)
        if (fileName.endsWith(".scala")) {
          val tacticGenClasses = new ScalaTacticCompiler().compile(source)
          assert(tacticGenClasses.size == 1, "Expected exactly 1 tactic generator class, but got " + tacticGenClasses.map(_.getName()))
          val tacticGenerator = tacticGenClasses.head.newInstance.asInstanceOf[()=> BelleExpr]
          Some(tacticGenerator())
        } else {
          Some(BelleParser(source))
        }
      case Some(t) if !File(t.toString).exists =>
        Some(BelleParser.parseWithInvGen(t.toString, None, defs, expandAll = false))
      case None => None
    }
  }

  case class ProofStatistics(name: String, tacticName: String, status: String, witness: Option[ProvableSig], timeout: Long,
                             duration: Long, qeDuration: Long, proofSteps: Int, tacticSize: Int) {
    def summary: String =
      s"""Proof Statistics ($name $status, with tactic $tacticName and time budget [s] $timeout)
         |Duration [ms]: $duration
         |QE [ms]: $qeDuration
         |Proof steps: $proofSteps
         |Tactic size: $tacticSize""".stripMargin

    override def toString: String = s"${status.toUpperCase} $name: tactic=$tacticName,tacticsize=$tacticSize,budget=$timeout[s],duration=$duration[ms],qe=$qeDuration[ms],steps=$proofSteps"

    def toCsv: String = s"$name,$tacticName,$status,${timeout*1000},$duration,$qeDuration,$proofSteps,$tacticSize"
  }

  /** Proves a single entry */
  private def prove(name: String, input: Formula, fileContent: String, defs: Declaration,
                    tacticName: String, tactic: BelleExpr, timeout: Long,
                    outputFileName: Option[String], options: OptionMap): ProofStatistics = {
    val inputSequent = Sequent(immutable.IndexedSeq[Formula](), immutable.IndexedSeq(input))

    //@note open print writer to create empty file (i.e., delete previous evidence if this proof fails).
    val pw = outputFileName.map(fn => new PrintWriter(URLEncoder.encode(fn, "UTF-8").
      replaceAllLiterally(URLEncoder.encode(File.separator, "UTF-8"), File.separator)))

    //@todo turn the following into a transformation as well. The natural type is Prover: Tactic=>(Formula=>Provable) which however always forces 'verify=true. Maybe that's not bad.

    val qeDurationListener = new IOListeners.StopwatchListener((_, t) => t match {
      case DependentTactic("QE") => true
      case DependentTactic("smartQE") => true
      case _ => false
    })

    val verbose = options.getOrElse('verbose, false).asInstanceOf[Boolean]
    val listeners =
      if (verbose) qeDurationListener :: new PrintProgressListener(tactic) :: Nil
      else qeDurationListener :: Nil
    BelleInterpreter.setInterpreter(LazySequentialInterpreter(listeners))

    val proofStatistics = try {
      qeDurationListener.reset()
      val proofStart: Long = Platform.currentTime
      implicit val ec: ExecutionContext = ExecutionContext.global
      val witness = Await.result(
        Future {
          TactixLibrary.proveBy(inputSequent, tactic)
        },
        if (timeout>0) Duration(timeout, TimeUnit.SECONDS) else Duration.Inf
      )
      val proofDuration = Platform.currentTime - proofStart
      val qeDuration = qeDurationListener.duration
      val proofSteps = witness.steps
      val tacticSize = TacticStatistics.size(tactic)

      if (witness.isProved) {
        assert(witness.subgoals.isEmpty)
        val expected = inputSequent.exhaustiveSubst(USubst(defs.substs))
        //@note pretty-printing the result of parse ensures that the lemma states what's actually been proved.
        insist(KeYmaeraXParser(KeYmaeraXPrettyPrinter(input)) == input, "parse of print is identity")
        //@note assert(witness.isProved, "Successful proof certificate") already checked in line above
        insist(witness.proved == expected, "Expected to have proved the original problem and not something else, but proved witness deviates from input")
        //@note check that proved conclusion is what we actually wanted to prove
        insist(witness.conclusion == expected, "Expected proved conclusion to be original problem, but proved conclusion deviates from input")

        //@note printing original input rather than a pretty-print of proved ensures that @invariant annotations are preserved for reproves.
        val evidence = ToolEvidence(List(
          "tool" -> "KeYmaera X",
          "model" -> fileContent,
          "tactic" -> tactic.prettyString,
          "proof" -> "" //@todo serialize proof
        )) :: Nil

        val lemma = outputFileName match {
          case Some(_) =>
            val lemma = Lemma(witness, evidence, Some(name))
            //@see[[edu.cmu.cs.ls.keymaerax.core.Lemma]]
            assert(lemma.fact.conclusion.ante.isEmpty && lemma.fact.conclusion.succ.size == 1, "Illegal lemma form")
            assert(KeYmaeraXExtendedLemmaParser(lemma.toString) == (lemma.name, lemma.fact.underlyingProvable, lemma.evidence),
              "reparse of printed lemma is not original lemma")
            Some(lemma)
          case None => None
        }

        pw match {
          case Some(w) =>
            assert(lemma.isDefined, "Lemma undefined even though writer is present")
            w.write(stampHead(options))
            w.write("/* @evidence: parse of print of result of a proof */\n\n")
            w.write(lemma.get.toString)
            w.close()
          case None =>
            // don't save proof as lemma since no outputFileName
        }

        ProofStatistics(name, tacticName, "proved", Some(witness), timeout, proofDuration, qeDuration, proofSteps, tacticSize)
      } else {
        // prove did not work
        assert(!witness.isProved)
        assert(witness.subgoals.nonEmpty)
        //@note instantiating PrintWriter above has already emptied the output file
        (pw, outputFileName) match {
          case (Some(w), Some(outName)) =>
            w.close()
            File(outName).delete()
          case _ =>
        }

        if (witness.subgoals.exists(s => s.ante.isEmpty && s.succ.head == False)) {
          ProofStatistics(name, tacticName, "unfinished (cex)", Some(witness), timeout, proofDuration, qeDuration, proofSteps, tacticSize)
        } else {
          ProofStatistics(name, tacticName, "unfinished", Some(witness), timeout, proofDuration, qeDuration, proofSteps, tacticSize)
        }
      }
    } catch {
      case _: TimeoutException =>
        BelleInterpreter.kill()
        // prover shutdown cleanup is done when KeYmaeraX exits
        ProofStatistics(name, tacticName, "timeout", None, timeout, -1, -1, -1, -1)
      case _: Throwable =>
        BelleInterpreter.kill()
        // prover shutdown cleanup is done when KeYmaeraX exits
        ProofStatistics(name, tacticName, "failed", None, timeout, -1, -1, -1, -1)
    }

    proofStatistics
  }

  /**
    * Proves all entries in the given archive file.
    * {{{KeYmaeraXLemmaPrinter(Prover(tactic)(KeYmaeraXProblemParser(input)))}}}
    *
    * @param options The prover options.
    */
  def prove(options: OptionMap): Unit = {
    if (options.contains('ptOut)) {
      ProvableSig.PROOF_TERMS_ENABLED = true
    } else {
      ProvableSig.PROOF_TERMS_ENABLED = false
    }

    require(options.contains('in), usage)
    val inputFileName = options('in).toString
    val inFiles = findFiles(inputFileName)
    val archiveContent = inFiles.map(p => p -> KeYmaeraXArchiveParser.parseFromFile(p.toFile.getAbsolutePath).filterNot(_.isExercise))
    println("Proving entries from " + archiveContent.size + " files")

    val conjectureFileName = options.get('conjecture).map(_.toString)
    val conjectureFiles = conjectureFileName.map(findFiles).getOrElse(List.empty)
    val conjectureContent = conjectureFiles.flatMap(p => KeYmaeraXArchiveParser.parseFromFile(p.toFile.getAbsolutePath).
      filterNot(_.isExercise).map(_ -> p).groupBy(_._1.name)).toMap
    val duplicateConjectures = conjectureContent.filter(_._2.size > 1)
    // conjectures must have unique names across files
    assert(duplicateConjectures.isEmpty, "Duplicate entry names in conjecture files:\n" + duplicateConjectures.map(c => c._1 + " in " + c._2.map(_._2).mkString(",")))
    // if exactly one conjecture and one solution: replace regardless of names; otherwise: insist on same entry names and replace by entry name
    val entryNamesDiff = archiveContent.flatMap(_._2.map(_.name)).toSet.diff(conjectureContent.keySet)
    assert(
      conjectureContent.isEmpty
        || (conjectureContent.map(_._2.size).sum == 1 && archiveContent.map(_._2.size).sum == 1)
        || entryNamesDiff.isEmpty, "Conjectures and archives must agree on names, but got diff " + entryNamesDiff.mkString(","))
    assert(conjectureContent.values.flatMap(_.flatMap(_._1.tactics)).isEmpty, "Conjectures must not list tactics")

    val outputFilePrefix = options.getOrElse('out, inputFileName).toString.stripSuffix(".kyp")
    val outputFileSuffix = ".kyp"
    //@note same archive entry name might be present in several .kyx files
    val outputFileNames: Map[Path, Map[ParsedArchiveEntry, String]] =
      if (archiveContent.size == 1 && archiveContent.head._2.size == 1)
        Map(archiveContent.head._1 -> Map(archiveContent.head._2.head -> (outputFilePrefix + outputFileSuffix)))
      else archiveContent.map({ case (path, entries) =>
        path -> entries.map(e => e -> (outputFilePrefix + "-" + path.getFileName + "-"
          + e.name.replaceAll("\\W", "_") + outputFileSuffix)).toMap
      }).toMap

    /** Replaces the conjecture of `entry` with the `conjecture`. */
    def replace(entry: ParsedArchiveEntry, conjecture: ParsedArchiveEntry): ParsedArchiveEntry = {
      conjecture.copy(tactics = entry.tactics)
    }

    val statistics = archiveContent.flatMap({case (path: Path, entries) =>
      entries.flatMap(entry => proveEntry(
        path,
        replace(entry, conjectureContent.getOrElse(entry.name,
          conjectureContent.headOption.map(_._2).getOrElse((entry -> path) :: Nil)).head._1),
        outputFileNames(path)(entry),
        options))
    })

    statistics.foreach(println)

    val csvStatistics = statistics.map(_.toCsv).mkString("\n")
    val statisticsLogger = Logger(getClass)
    statisticsLogger.info(MarkerManager.getMarker("PROOF_STATISTICS"), csvStatistics)

    if (statistics.exists(_.status=="disproved")) sys.exit(-2)
    if (statistics.exists(_.status=="unfinished")) sys.exit(-1)
  }

  private def proveEntry(path: Path, entry: ParsedArchiveEntry, outputFileName: String,
                         options: OptionMap): List[ProofStatistics] = {
    def savePt(pt: ProvableSig): Unit = {
      (pt, options.get('ptOut)) match {
        case (ptp: TermProvable, Some(path: String)) =>
          val conv = new IsabelleConverter(ptp.pt)
          val source = conv.sexp
          val writer = new PrintWriter(path)
          writer.write(source)
          writer.close()
        case (_, None) => ()
        case (_: TermProvable, None) => assert(false, "Proof term output path specified but proof did not contain proof term")
      }
    }

    val qeDurationListener = new IOListeners.StopwatchListener((_, t) => t match {
      case DependentTactic("QE") => true
      case DependentTactic("smartQE") => true
      case _ => false
    })

    val verbose = options.getOrElse('verbose, false).asInstanceOf[Boolean]
    val tacticString = readTactic(options, entry.defs)
    val reqTacticName = options.get('tacticName)
    val timeout = options.getOrElse('timeout, 0L).asInstanceOf[Long]

    //@note open print writer to create empty file (i.e., delete previous evidence if this proof fails).
    new PrintWriter(URLEncoder.encode(outputFileName, "UTF-8").
      replaceAllLiterally(URLEncoder.encode(File.separator, "UTF-8"), File.separator))

    val t = tacticString match {
      case Some(tac) => ("user", "user", tac) :: Nil
      case None =>
        if (reqTacticName.isDefined) entry.tactics.filter(_._1 == reqTacticName.get)
        else if (entry.tactics.isEmpty) ("auto", "auto", TactixLibrary.auto) :: Nil
        else entry.tactics
    }

    println("Proving " + path + "#" + entry.name + " ...")
    if (t.isEmpty) {
      println("Unknown tactic " + reqTacticName + ", skipping entry")
      ProofStatistics(entry.name, reqTacticName.getOrElse("auto").toString, "skipped", None, timeout, -1, -1, -1, -1) :: Nil
    } else {
      t.zipWithIndex.map({ case ((tacticName, _, tactic), i) =>
        val listeners =
          if (verbose) qeDurationListener :: new PrintProgressListener(tactic) :: Nil
          else qeDurationListener :: Nil
        BelleInterpreter.setInterpreter(LazySequentialInterpreter(listeners))

        val proofStat = prove(entry.name, entry.model.asInstanceOf[Formula], entry.fileContent, entry.defs, tacticName, tactic,
          timeout, if (i == 0) Some(outputFileName) else None, options)

        proofStat.witness match {
          case Some(proof) =>
            if (entry.kind == "lemma") {
              val lemmaName = "user" + File.separator + entry.name
              if (LemmaDBFactory.lemmaDB.contains(lemmaName)) LemmaDBFactory.lemmaDB.remove(lemmaName)
              val evidence = Lemma.requiredEvidence(proof, ToolEvidence(List(
                "tool" -> "KeYmaera X",
                "model" -> entry.fileContent,
                "tactic" -> entry.tactics.head._2
              )) :: Nil)
              LemmaDBFactory.lemmaDB.add(new Lemma(proof, evidence, Some(lemmaName)))
            }
            savePt(proof)
          case None => // nothing to do
        }
        proofStat
      })
    }
  }

  /**
   * ModelPlex monitor synthesis for the given input files
   * {{{KeYmaeraXPrettyPrinter(ModelPlex(vars)(KeYmaeraXProblemParser(input))}}}
   *
   * @param options in describes input file name, vars describes the list of variables, out describes the output file name.
   */
  def modelplex(options: OptionMap): Unit = {
    //@TODO remove option, hol config no longer necessary
    if (options.contains('ptOut)) {
      //@TODO: Actual produce proof terms here, right now this option is overloaded to produce hol config instead
      ProvableSig.PROOF_TERMS_ENABLED = false
    } else {
      ProvableSig.PROOF_TERMS_ENABLED = false
    }
    require(options.contains('in), usage)

    val in = options('in).toString
    val inputEntry = KeYmaeraXArchiveParser.parseFromFile(in).head
    val inputModel = inputEntry.model.asInstanceOf[Formula]

    val verifyOption: Option[ProvableSig => Unit] =
      if (options.getOrElse('verify, false).asInstanceOf[Boolean]) {
        Some({case ptp:TermProvable =>
          val conv = new IsabelleConverter(ptp.pt)
          val source = conv.sexp
          val pwPt = new PrintWriter(options('ptOut).asInstanceOf[String]+".pt")
          pwPt.write(source)
          pwPt.close()
        case _:ProvableSig => ()
        })
      } else Some{case _ => ()}
    //val isarOption = options.getOrElse('isar,false).asInstanceOf[Boolean]

    val inputFileName = in.split('#')(0).dropRight(4)

    val outputFileName =
      if (options.contains('out)) options('out).toString
      else inputFileName + ".kym"

    val kind =
      if (options.contains('sandbox)) 'sandbox
      else if (options.contains('monitor)) options('monitor).asInstanceOf[Symbol]
      else 'model

    if (options.contains('sandbox)) {
      val fallback = options.get('fallback) match {
        case Some(fallbackPrgString: String) => fallbackPrgString.asProgram
        case _ => inputEntry.model match {
          case Imply(_, Box(Loop(Compose(ctrl, _)), _)) => ctrl
          case Imply(_, Box(Compose(ctrl, _), _)) => ctrl
          case _ => throw new IllegalArgumentException("Unable to extract fallback from input model. Please provide fallback program with option -fallback.")
        }
      }

      //check safety proof
      println(s"Checking safety proof ${inputEntry.name}...")
      assert(TactixLibrary.proveBy(inputEntry.model.asInstanceOf[Formula], inputEntry.tactics.head._3).isProved,
        s"Sandbox synthesis requires a provably safe input model, but ${inputEntry.name} is not proved.")
      println(s"Done checking safety proof ${inputEntry.name}")

      println("Synthesizing sandbox and safety proof...")
      val ((sandbox, sbTactic), lemmas) = ModelPlex.createSandbox(
        inputEntry.name,
        inputEntry.tactics.head._3,
        Some(fallback),
        kind = 'ctrl,
        checkProvable =  None)(inputModel)
      println("Done synthesizing sandbox and safety proof")

      val db = new TempDBTools(Nil)

      val lemmaEntries = lemmas.map({ case (name, fml, tactic) =>
        val serializableTactic = db.extractSerializableTactic(fml, tactic)
        ParsedArchiveEntry(name, "lemma", "", "", Declaration(Map.empty), fml,
          (name + " Proof", BellePrettyPrinter(serializableTactic), serializableTactic)::Nil, Nil, Map.empty)})
      // check and store lemmas
      lemmaEntries.foreach(entry => {
        println(s"Checking sandbox lemma ${entry.name}...")
        val lemmaProof = TactixLibrary.proveBy(entry.model.asInstanceOf[Formula], entry.tactics.head._3)
        assert(lemmaProof.isProved, s"Aborting sandbox synthesis: sandbox lemma ${entry.name} was not provable.")
        println(s"Done checking sandbox lemma ${entry.name}")
        val lemmaName = "user" + File.separator + entry.name
        if (LemmaDBFactory.lemmaDB.contains(lemmaName)) LemmaDBFactory.lemmaDB.remove(lemmaName)
        val evidence = Lemma.requiredEvidence(lemmaProof, ToolEvidence(List(
          "tool" -> "KeYmaera X",
          "model" -> entry.fileContent,
          "tactic" -> entry.tactics.head._2
        )) :: Nil)
        LemmaDBFactory.lemmaDB.add(new Lemma(lemmaProof, evidence, Some(lemmaName)))
      })

      val serializableTactic = db.extractSerializableTactic(sandbox, sbTactic)
      val sandboxEntry = ParsedArchiveEntry(inputEntry.name + " Sandbox", "theorem", "", "", Declaration(Map.empty),
        sandbox, (inputEntry.name + " Sandbox Proof", BellePrettyPrinter(serializableTactic), serializableTactic)::Nil, Nil, Map.empty)
      // check sandbox proof
      println("Checking sandbox safety...")
      assert(TactixLibrary.proveBy(sandboxEntry.model.asInstanceOf[Formula],
        sandboxEntry.tactics.head._3).isProved,
        "Aborting sandbox synthesis: sandbox safety was not derivable from input model safety proof.")
      println("Done checking sandbox safety")

      val archive = (lemmaEntries :+ sandboxEntry).map(new KeYmaeraXArchivePrinter()(_)).mkString("\n\n")
      val pw = new PrintWriter(outputFileName)
      pw.write(archive)
      pw.close()
      println(s"Sandbox synthesis successful: $outputFileName")
    } else if (options.contains('vars)) {
      val result = ModelPlex(options('vars).asInstanceOf[Array[Variable]].toList, kind, verifyOption)(inputModel)
      printModelplexResult(inputModel, result, outputFileName, options)
    } else {
      val result = ModelPlex(inputModel, kind, verifyOption)
      printModelplexResult(inputModel, result, outputFileName, options)
    }
  }

  private def printModelplexResult(model: Formula, fml: Formula, outputFileName: String, options: OptionMap): Unit = {
    val output = KeYmaeraXPrettyPrinter(fml)
    val reparse = KeYmaeraXParser(output)
    assert(reparse == fml, "parse of print is identity")
    val pw = new PrintWriter(outputFileName)
    pw.write(stampHead(options))
    pw.write("/* @evidence: parse of print of ModelPlex proof output */\n\n")
    pw.write("/************************************\n * Generated by KeYmaera X ModelPlex\n ************************************/\n\n")
    pw.write("/**\n * @param variables are for the state before the controller run\n * @param post() function symbols are for the state after the controller run\n * @param other function symbols are constant\n */\n\n")
    pw.write(output)
    pw.close()

    options.get('ptOut) match {
      case Some(path:String) =>
        val pwHOL = new PrintWriter(outputFileName + ".holconfiggen")
        // @TODO: Robustify
        val Imply(init, Box(Compose(Test(bounds),Loop(Compose(ctrl,plant))),safe)) = model
        val consts = StaticSemantics.signature(model)
        pwHOL.write(HOLConverter.configFile(consts,options('vars).asInstanceOf[Array[Variable]].toList,bounds,init,fml))
        pwHOL.close()

      case None => ()
    }
  }

  def repl(options: OptionMap): Unit = {
    require(options.contains('model), usage)
    val modelFileNameDotKyx = options('model).toString
    val tacticFileNameDotKyt = options.get('tactic).map(_.toString)
    val scaladefsFilename = options.get('scaladefs).map(_.toString)
    assert(modelFileNameDotKyx.endsWith(".kyx"),
      "\n[Error] Wrong model file name " + modelFileNameDotKyx + " used for -repl! Should. Please use: -repl MODEL.kyx TACTIC.kyt")
    tacticFileNameDotKyt.foreach(name => assert(name.endsWith(".kyt"), "\n[Error] Wrong tactic file name " + tacticFileNameDotKyt + " used for -repl! Should. Please use: -repl MODEL.kyx TACTIC.kyt"))
    val modelInput = managed(scala.io.Source.fromFile(modelFileNameDotKyx, "ISO-8859-1")).apply(_.mkString)
    val tacticInput = tacticFileNameDotKyt.map(f => managed(scala.io.Source.fromFile(f, "ISO-8859-1")).apply(_.mkString))
    val defsInput = scaladefsFilename.map(f => managed(scala.io.Source.fromFile(f, "ISO-8859-1")).apply(_.mkString))
    val inputFormula: Formula = KeYmaeraXArchiveParser.parseAsProblemOrFormula(modelInput)
    new BelleREPL(inputFormula, tacticInput, defsInput, tacticFileNameDotKyt, scaladefsFilename).run()
  }

  /**
   * Code generation
   * {{{CGenerator()(input)}}}
   */
  def codegen(options: OptionMap): Unit = {
    require(options.contains('in), usage)

    val inputFileName = options('in).toString
    val inputFile =
      if (inputFileName.contains("#")) File(inputFileName.substring(0, inputFileName.lastIndexOf("#")))
      else File(inputFileName)

    val inputFormulas = KeYmaeraXArchiveParser.parseFromFile(inputFileName)
    var outputFile = inputFile.changeExtension("c")
    if (options.contains('out)) outputFile = File(options('out).toString)

    val vars: Option[Set[BaseVariable]] =
      if (options.contains('vars)) Some(options('vars).asInstanceOf[Array[BaseVariable]].toSet)
      else None

    val interval = options.getOrElse('interval, true).asInstanceOf[Boolean]
    val head = stampHead(options)
    val quantitative = options.get('quantitative)
    val written = inputFormulas.map(e => {
      val outputFileName =
        if (inputFormulas.size <= 1) outputFile.toString()
        else {
          val ext = outputFile.extension
          outputFile.addExtension(e.name.replaceAll("\\s", "_")).addExtension(ext).toString()
        }
      if (quantitative.isDefined) codegenQuantitative(e, outputFileName, head, vars, quantitative.get.toString)
      else codegen(e, interval, outputFileName, head, vars)
      outputFileName
    })
    println("Generated\n  " + written.mkString("\n  "))
  }

  def codegen(entry: ParsedArchiveEntry, interval: Boolean, outputFileName: String, head: String,
              vars: Option[Set[BaseVariable]]): Unit = {
    if (interval) {
      //@todo check that when assuming the output formula as an additional untrusted lemma, the Provable isProved.
      System.err.println("Cannot yet augment compiled code with interval arithmetic to guard against floating-point roundoff errors\n(use -nointerval instead)")

      println("Interval arithmetic: unfinished")
      System.err.println("Interval arithmetic: unfinished")
      //@todo wipe out output file PrintWriter above has already emptied the output file
      //@todo pw.close()
      exit(-1)
      // TODO what to to when proof cannot be checked?
    } else {
      println("Interval arithmetic: Skipped interval arithmetic generation\n(use -interval to guard against floating-point roundoff errors)")
    }

    val inputFormula = entry.model.asInstanceOf[Formula]

    //@note codegen in C format only regardless of file extension
    val theVars = vars match {
      case Some(v) => v
      case None => StaticSemantics.vars(inputFormula).symbols.filter(_.isInstanceOf[BaseVariable]).map(_.asInstanceOf[BaseVariable])
    }

    val codegenStart = Platform.currentTime
    //@todo input variables (nondeterministically assigned in original program)
    val output = (new CGenerator(new CMonitorGenerator()))(inputFormula, theVars, Set(), outputFileName)
    Console.println("[codegen time " + (Platform.currentTime - codegenStart) + "ms]")
    val pw = new PrintWriter(outputFileName)
    pw.write(head)
    pw.write("/* @evidence: print of CGenerator of input */\n\n")
    pw.write(output._1 + "\n" + output._2)
    pw.close()
  }

  def codegenQuantitative(entry: ParsedArchiveEntry, outputFileName: String, head: String,
                          vars: Option[Set[BaseVariable]], kind: String): Unit = {
    import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
    val (monitorFml: Formula, monitorStateVars: Set[BaseVariable]) =
      if (entry.model.asInstanceOf[Formula].isFOL) {
        val stateVars = vars match {
          case Some(v) => v
          case None => StaticSemantics.vars(entry.model).symbols.filter(_.isInstanceOf[BaseVariable]).map(_.asInstanceOf[BaseVariable])
        }
        (entry.model.asInstanceOf[Formula], stateVars)
      } else {
        val model@Imply(_, Box(Loop(Compose(prg, _)), _)) = entry.model

        val nonlinearModelApprox = ModelPlex.createNonlinearModelApprox(entry.name, entry.tactics.head._3)(model)
        val Imply(init, Box(Loop(Compose(
          ctrl,
          plant@Compose(x0Ghosts, Compose(Test(x0EvolDomain), Compose(nondetPlant, Test(evolDomain)))))), safe)) = nonlinearModelApprox._1

        val monitorStateVars = vars match {
          case Some(v) => v.toSeq
          case None => kind match {
            case "model" => StaticSemantics.boundVars(nonlinearModelApprox._1).symbols.toSeq
            case "ctrl" => StaticSemantics.boundVars(ctrl).symbols.toSeq
            case "plant" => StaticSemantics.boundVars(plant).symbols.toSeq
          }
        }

        val (monitorInput, assumptions) = kind match {
          case "model" => ModelPlex.createMonitorSpecificationConjecture(nonlinearModelApprox._1, monitorStateVars: _*)
          case "ctrl" => ModelPlex.createMonitorSpecificationConjecture(Imply(init, Box(Loop(ctrl), safe)), monitorStateVars: _*)
          case "plant" => ModelPlex.createMonitorSpecificationConjecture(Imply(init, Box(Loop(plant), safe)), monitorStateVars: _*)
        }

        val simplifier = SimplifierV3.simpTac(taxs = SimplifierV3.composeIndex(
          SimplifierV3.groundEqualityIndex, SimplifierV3.defaultTaxs))
        val monitorTactic = DebuggingTactics.print("Deriving Monitor") &
          ModelPlex.controllerMonitorByChase(1) &
          DebuggingTactics.print("Chased") &
          SaturateTactic(ModelPlex.optimizationOneWithSearch(ToolProvider.simplifierTool(), assumptions)(1)) &
          DebuggingTactics.print("Quantifiers instantiated") &
          simplifier(1) & DebuggingTactics.print("Monitor Result")

        val monitorResult = TactixLibrary.proveBy(monitorInput, monitorTactic)
        val monitorFml = monitorResult.subgoals.head.succ.head
        (monitorFml, monitorStateVars.toSet)
      }

    val reassociatedMonitorFml = FormulaTools.reassociate(monitorFml)
    //proveBy(Equiv(modelMonitorFml, reassociatedCtrlMonitorFml), TactixLibrary.prop)
    val monitorProg = TactixLibrary.proveBy(reassociatedMonitorFml, ModelPlex.chaseToTests(combineTests=false)(1)*2).subgoals.head.succ.head
    val inputs = CGenerator.getInputs(monitorProg)
    val monitorCode = (new CGenerator(new CMonitorGenerator()))(monitorProg, monitorStateVars, inputs, "Monitor")

    val pw = new PrintWriter(outputFileName)
    pw.write(head)
    pw.write("/* @evidence: print of CGenerator of input */\n\n")
    pw.write(monitorCode._1 + "\n" + monitorCode._2)
    pw.close()
  }

  /** Strips proof hints from the model. */
  def stripHints(options: OptionMap): Unit = {
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

  /** Launch the web user interface */
  def launchUI(args: Array[String]): Unit = {
    val augmentedArgs = if (args.map(_.stripPrefix("-")).intersect(Modes.modes.toList).isEmpty) args :+ Modes.UI else args
    if (LAUNCH) Main.main("-launch" +: augmentedArgs)
    else Main.main(augmentedArgs)
  }
  
  // helpers

  /** Print brief information about all open goals in the proof tree under node */
  def printOpenGoals(node: ProvableSig): Unit = node.subgoals.foreach(g => printNode(g))

  def printNode(node: Sequent): Unit = node.toString + "\n"

  /** Implements the security policy for the KeYmaera X web server.
    *
    * Preferably we would heavily restrict uses of reflection (to prevent, for example, creating fake Provables),
    * but we know of no way to do so except relying on extremely fragile methods such as crawling the call stack.
    * The same goes for restricting read access to files.
    *
    * Instead we settle for preventing people from installing less-restrictive security managers and restricting
    * all writes to be inside the .keymaerax directory. */
  class KeYmaeraXSecurityManager extends SecurityManager {
    override def checkPermission(perm: Permission): Unit = {
      perm match {
          //@todo should disallow writing reflection in .core.
        case perm:ReflectPermission if "suppressAccessChecks"==perm.getName =>
          throw new SecurityException("suppressing access checks during reflection is forbidden")
        case _:ReflectPermission => ()
        case _:RuntimePermission =>
          if ("setSecurityManager".equals(perm.getName))
            throw new SecurityException("Changing security manager is forbidden")
        case _:FilePermission =>
          val filePermission = perm.asInstanceOf[FilePermission]
          val name = filePermission.getName
          val actions = filePermission.getActions
          if ((actions.contains("write") || actions.contains("delete"))
            && !name.startsWith(Configuration.KEYMAERAX_HOME_PATH)) {
            throw new SecurityException("KeYmaera X security manager forbids writing to files outside " + Configuration.KEYMAERAX_HOME_PATH)
          }
      }
    }
  }

  private def activateSecurity(): Unit = {
    System.setSecurityManager(new KeYmaeraXSecurityManager())
  }

  private val interactiveUsage = "Type a tactic command to apply to the current goal.\n" +
    "skip - ignore the current goal for now and skip to the next goal.\n" +
    "goals - list all open goals.\n" +
    "goal i - switch to goal number i\n" +
    "exit - quit the prover (or hit Ctrl-C any time).\n" +
    "help - will display this usage information.\n" +
    "Tactics will be reported back when a branch closes but may need cleanup.\n"

  /** KeYmaera C: A simple interactive command-line prover */
  @deprecated("Use web UI instead")
  private def interactiveProver(root: ProvableSig): ProvableSig = {
    val commands = io.Source.stdin.getLines()
    println("KeYmaera X Interactive Command-line Prover\n" +
      "If you are looking for the more convenient web user interface,\nrestart with option -ui\n\n")
    println(interactiveUsage)

    while (!root.isProved) {
      assert(root.subgoals.nonEmpty, "proofs that are not closed must have open goals")
      println("Open Goals: " + root.subgoals.size)
      var node = root.subgoals.head
      var current = root
      //println("=== " + node.tacticInfo.infos.getOrElse("branchLabel", "<none>") + " ===\n")
      var tacticLog = ""
      assert(!current.isProved, "open goals are not closed")
      while (!current.isProved) {
        printNode(node)
        System.out.flush()
        commands.next().trim match {
          case "" =>
          case "help" => println(interactiveUsage)
          case "exit" => exit(5)
          case "goals" => val open = root.subgoals
            (1 to open.length).foreach(g => {println("Goal " + g); printNode(open(g-1))})
          case it if it.startsWith("goal ") => try {
            val g = it.substring("goal ".length).toInt
            if (1<=g&&g<=root.subgoals.size) node = root.subgoals(g-1)
            else println("No such goal: "+ g)
          } catch {case e: NumberFormatException => println(e)}
          case "skip" =>
            if (root.subgoals.size >= 2) {
              //@todo skip to the next goal somewhere on the right of node, not to a random goal
              //@todo track this level skipping by closing and opening parentheses in the log
              var nextGoal = new Random().nextInt(root.subgoals.length)
              assert(0 <= nextGoal && nextGoal < root.subgoals.size, "random in range")
              node = if (root.subgoals(nextGoal) != node)
                root.subgoals(nextGoal)
              else {
                val otherGoals = root.subgoals diff List(node)
                assert(otherGoals.length == root.subgoals.length - 1, "removing one open goal decreases open goal count by 1")
                nextGoal = new Random().nextInt(otherGoals.length)
                assert(0 <= nextGoal && nextGoal < otherGoals.size, "random in range")
                otherGoals(nextGoal)
              }
            } else {
              println("No other open goals to skip to")
            }
          case command: String =>
            //@note security issue since executing arbitrary input unsanitized
            val tacticGenerator = new ScalaTacticCompiler().compile(tacticParsePrefix + command + tacticParseSuffix).head.newInstance().asInstanceOf[() => BelleExpr]
            val tactic = tacticGenerator()
            tacticLog += "& " + command + "\n"
            current = TactixLibrary.proveBy(node, tactic)
            // walk to the next open subgoal
            // continue walking if it has leaves
            while (!current.isProved && current.subgoals.nonEmpty)
              node = current.subgoals.head
            //@todo make sure to walk to siblings ultimately
        }
      }
      assert(current.isProved)
//      println("=== " + node.tacticInfo.infos.getOrElse("branchLabel", "<none>") + " === CLOSED")
      println(tacticLog)
    }
    root
  }

  /** Finds files matching the pattern in fileName (specific file or using glob wildcards). */
  private def findFiles(fileName: String): List[Path] = {
    // specific file, no wildcard support when referring to a specific entry
    if (new java.io.File(fileName).exists || fileName.contains("#")) Paths.get(fileName).toAbsolutePath :: Nil
    else {
      val path = Paths.get(fileName).toAbsolutePath
      val dir = path.getParent
      val pattern = path.getFileName
      val finder = new SimpleFileVisitor[Path] {
        private val matcher = FileSystems.getDefault.getPathMatcher("glob:" + pattern)
        val files: ListBuffer[Path] = new ListBuffer[Path]()
        override def visitFile(file: Path, attrs: BasicFileAttributes): FileVisitResult = {
          if (matcher.matches(file.getFileName)) files.append(file)
          FileVisitResult.CONTINUE
        }
      }
      Files.walkFileTree(dir, finder)
      finder.files.toList
    }
  }

  //@todo import namespace of the user tactic *object* passed in -tactic
  private val tacticParsePrefix =
    """
      |import edu.cmu.cs.ls.keymaerax.bellerophon._
      |import edu.cmu.cs.ls.keymaerax.btactics._
      |import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
      |import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._
      |import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
      |class InteractiveLocalTactic extends (() => BelleExpr) {
      |  def apply(): BelleExpr = {
      |
    """.stripMargin

  private val tacticParseSuffix =
    """
      |  }
      |}
    """.stripMargin


  private val license: String =
    """
      |KeYmaera X
      |SOFTWARE LICENSE AGREEMENT
      |ACADEMIC OR NON-PROFIT ORGANIZATION NONCOMMERCIAL RESEARCH USE ONLY
      |
      |BY USING THE SOFTWARE, YOU ARE AGREEING TO THE TERMS OF THIS LICENSE
      |AGREEMENT. IF YOU DO NOT AGREE WITH THESE TERMS, YOU MAY NOT USE OR
      |DOWNLOAD THE SOFTWARE.
      |
      |This is a license agreement ("Agreement") between your academic
      |institution or non-profit organization or self (called "Licensee" or
      |"You" in this Agreement) and Carnegie Mellon University (called
      |"Licensor" in this Agreement). All rights not specifically granted
      |to you in this Agreement are reserved for Licensor.
      |
      |RESERVATION OF OWNERSHIP AND GRANT OF LICENSE:
      |
      |Licensor retains exclusive ownership of any copy of the Software (as
      |defined below) licensed under this Agreement and hereby grants to
      |Licensee a personal, non-exclusive, non-transferable license to use
      |the Software for noncommercial research purposes, without the right
      |to sublicense, pursuant to the terms and conditions of this
      |Agreement. As used in this Agreement, the term "Software" means (i)
      |the executable file made accessible to Licensee by Licensor pursuant
      |to this Agreement, inclusive of backups, and updates permitted
      |hereunder or subsequently supplied by Licensor, including all or any
      |file structures, programming instructions, user interfaces and
      |screen formats and sequences as well as any and all documentation
      |and instructions related to it.
      |
      |CONFIDENTIALITY: Licensee acknowledges that the Software is
      |proprietary to Licensor, and as such, Licensee agrees to receive all
      |such materials in confidence and use the Software only in accordance
      |with the terms of this Agreement. Licensee agrees to use reasonable
      |effort to protect the Software from unauthorized use, reproduction,
      |distribution, or publication.
      |
      |COPYRIGHT: The Software is owned by Licensor and is protected by
      |United States copyright laws and applicable international treaties
      |and/or conventions.
      |
      |PERMITTED USES: The Software may be used for your own noncommercial
      |internal research purposes. You understand and agree that Licensor
      |is not obligated to implement any suggestions and/or feedback you
      |might provide regarding the Software, but to the extent Licensor
      |does so, you are not entitled to any compensation related thereto.
      |
      |BACKUPS: If Licensee is an organization, it may make that number of
      |copies of the Software necessary for internal noncommercial use at a
      |single site within its organization provided that all information
      |appearing in or on the original labels, including the copyright and
      |trademark notices are copied onto the labels of the copies.
      |
      |USES NOT PERMITTED: You may not modify, translate, reverse engineer,
      |decompile, disassemble, distribute, copy or use the Software except
      |as explicitly permitted herein. Licensee has not been granted any
      |trademark license as part of this Agreement and may not use the name
      |or mark "KeYmaera X", "Carnegie Mellon" or any renditions thereof
      |without the prior written permission of Licensor.
      |
      |You may not sell, rent, lease, sublicense, lend, time-share or
      |transfer, in whole or in part, or provide third parties access to
      |prior or present versions (or any parts thereof) of the Software.
      |
      |ASSIGNMENT: You may not assign this Agreement or your rights
      |hereunder without the prior written consent of Licensor. Any
      |attempted assignment without such consent shall be null and void.
      |
      |TERM: The term of the license granted by this Agreement is from
      |Licensee's acceptance of this Agreement by clicking "I Agree" below
      |or by using the Software until terminated as provided below.
      |
      |The Agreement automatically terminates without notice if you fail to
      |comply with any provision of this Agreement. Licensee may terminate
      |this Agreement by ceasing using the Software. Upon any termination
      |of this Agreement, Licensee will delete any and all copies of the
      |Software. You agree that all provisions which operate to protect the
      |proprietary rights of Licensor shall remain in force should breach
      |occur and that the obligation of confidentiality described in this
      |Agreement is binding in perpetuity and, as such, survives the term
      |of the Agreement.
      |
      |FEE: Provided Licensee abides completely by the terms and conditions
      |of this Agreement, there is no fee due to Licensor for Licensee's
      |use of the Software in accordance with this Agreement.
      |
      |DISCLAIMER OF WARRANTIES: THE SOFTWARE IS PROVIDED "AS-IS" WITHOUT
      |WARRANTY OF ANY KIND INCLUDING ANY WARRANTIES OF PERFORMANCE OR
      |MERCHANTABILITY OR FITNESS FOR A PARTICULAR USE OR PURPOSE OR OF
      |NON-INFRINGEMENT. LICENSEE BEARS ALL RISK RELATING TO QUALITY AND
      |PERFORMANCE OF THE SOFTWARE AND RELATED MATERIALS.
      |
      |SUPPORT AND MAINTENANCE: No Software support or training by the
      |Licensor is provided as part of this Agreement.
      |
      |EXCLUSIVE REMEDY AND LIMITATION OF LIABILITY: To the maximum extent
      |permitted under applicable law, Licensor shall not be liable for
      |direct, indirect, special, incidental, or consequential damages or
      |lost profits related to Licensee's use of and/or inability to use
      |the Software, even if Licensor is advised of the possibility of such
      |damage.
      |
      |EXPORT REGULATION: Licensee agrees to comply with any and all
      |applicable U.S. export control laws, regulations, and/or other laws
      |related to embargoes and sanction programs administered by the
      |Office of Foreign Assets Control.
      |
      |SEVERABILITY: If any provision(s) of this Agreement shall be held to
      |be invalid, illegal, or unenforceable by a court or other tribunal
      |of competent jurisdiction, the validity, legality and enforceability
      |of the remaining provisions shall not in any way be affected or
      |impaired thereby.
      |
      |NO IMPLIED WAIVERS: No failure or delay by Licensor in enforcing any
      |right or remedy under this Agreement shall be construed as a waiver
      |of any future or other exercise of such right or remedy by Licensor.
      |
      |GOVERNING LAW: This Agreement shall be construed and enforced in
      |accordance with the laws of the Commonwealth of Pennsylvania without
      |reference to conflict of laws principles. You consent to the
      |personal jurisdiction of the courts of this County and waive their
      |rights to venue outside of Allegheny County, Pennsylvania.
      |
      |ENTIRE AGREEMENT AND AMENDMENTS: This Agreement constitutes the sole
      |and entire agreement between Licensee and Licensor as to the matter
      |set forth herein and supersedes any previous agreements,
      |understandings, and arrangements between the parties relating hereto.
      |
    """.stripMargin
}
