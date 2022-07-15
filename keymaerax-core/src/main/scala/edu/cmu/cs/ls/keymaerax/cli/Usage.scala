/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.tools.install.DefaultConfiguration

/** Provides usages information. */
object Usage {
  /** Prints help messages for command line options. */
  def optionErrorReporter(option: String, usage: String): Unit = {
    val noValueMessage = "[Error] No value specified for " + option + " option. "
    option match {
      case "-prove" => println(noValueMessage + "Please use: -prove FILENAME.[key/kyx]\n\n" + usage)
      case "-modelPlex" => println(noValueMessage + "Please use: -modelPlex FILENAME.[key/kyx]\n\n" + usage)
      case "-codegen" => println(noValueMessage + "Please use: -codegen FILENAME.kym\n\n" + usage)
      case "-convert" => println(noValueMessage + "Please use: -convert [stripHints|verboseTactics|verbatimTactics] FILENAME.kyx\n\n" + usage)
      case "-out" => println(noValueMessage + "Please use: -out FILENAME.proof | FILENAME.kym | FILENAME.c | FILENAME.g\n\n" + usage)
      case "-conjecture" => println(noValueMessage + "Please use: -conjecture FILENAME.kyx\n\n" + usage)
      case "-vars" => println(noValueMessage + "Please use: -vars VARIABLE_1,VARIABLE_2,...\n\n" + usage)
      case "-tactic" =>  println(noValueMessage + "Please use: -tactic FILENAME.[scala|kyt]\n\n" + usage)
      case "-mathkernel" => println(noValueMessage + "Please use: -mathkernel PATH_TO_" + DefaultConfiguration.defaultMathLinkName._1 + "_FILE\n\n" + usage)
      case "-jlink" => println(noValueMessage + "Please use: -jlink PATH_TO_DIRECTORY_CONTAINS_" +  DefaultConfiguration.defaultMathLinkName._2 + "_FILE\n\n" + usage)
      case "-tool" => println(noValueMessage + "Please use: -tool mathematica|wolframengine|z3\n\n" + usage)
      case "-grade" => println(noValueMessage + "Please use: -grade FILENAME.json [-exportanswers [-out DIR]] [-skiponparseerror]\n\n" + usage)
      case _ =>  println("[Error] Unknown option " + option + "\n\n" + usage)
    }
  }

  /** Usage -help information.
    * @note Formatted to 80 characters terminal width. */
  private val usage: String =
    """Usage: java -jar keymaerax.jar
      |  -ui [web server options] |
      |  -prove file.kyx [-conjecture file2.kyx] [-out file.kyp]
      |     [-timeout seconds] [-verbose] |
      |  -modelplex file.kyx [-monitor ctrl|model] [-out file.kym] [-isar]
      |     [-sandbox] [-fallback prg] |
      |  -codegen file.kym [-vars var1,var2,..,varn] [-out file.c]
      |     [-quantitative] |
      |  -convert [stripHints|kyx2mat|kyx2smt|mat2kyx|mat2smt|smt2kyx|smt2mat] file.kyx [-out fileout.kyx]
      |  -setup
      |
      |Actions:
      |  -ui        start web user interface with optional server arguments (default)
      |  -prove     run prover on given archive of models or proofs
      |  -modelplex synthesize monitor from given model by proof with ModelPlex tactic
      |  -codegen   generate executable C code from given model file
      |  -convert   model and tactic conversions
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

  /** Command-line interface usage. */
  val cliUsage: String = usage.linesWithSeparators.filter(_ != "  -ui [web server options] |\n").mkString
  /** Full usage. */
  val fullUsage: String = usage
}
