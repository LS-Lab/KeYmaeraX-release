/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

/** Provides usages information. */
object Usage {

  /** Prints help messages for command line options. */
  def optionErrorReporter(option: String): Unit = {
    val noValueMessage = s"[Error] No value specified for option $option."
    option match {
      case "-prove" => println(s"$noValueMessage Please use: -prove FILENAME.[key/kyx]")
      case "-modelPlex" => println(s"$noValueMessage Please use: -modelPlex FILENAME.[key/kyx]")
      case "-codegen" => println(s"$noValueMessage Please use: -codegen FILENAME.kym")
      case "-convert" =>
        println(s"$noValueMessage Please use: -convert [stripHints|verboseTactics|verbatimTactics] FILENAME.kyx")
      case "-out" =>
        println(s"$noValueMessage Please use: -out FILENAME.proof | FILENAME.kym | FILENAME.c | FILENAME.g")
      case "-conjecture" => println(s"$noValueMessage Please use: -conjecture FILENAME.kyx")
      case "-vars" => println(s"$noValueMessage Please use: -vars VARIABLE_1,VARIABLE_2,...")
      case "-tactic" => println(s"$noValueMessage Please use: -tactic FILENAME.[scala|kyt]")
      case "-mathkernel" => println(s"$noValueMessage Please use: -mathkernel PATH_TO_MATH_KERNEL")
      case "-jlink" => println(s"$noValueMessage Please use: -jlink PATH_TO_DIRECTORY_CONTAINING_JLINK_LIB")
      case "-jlinktcpip" => println(s"$noValueMessage Please use: -jlinktcpip [true|false]")
      case "-jlinkinterface" => println(s"$noValueMessage Please use: -jlinkinterface [string|expr]")
      case "-parallelqe" => println(s"$noValueMessage Please use: -parallelqe [true|false]")
      case "-qemethod" => println(s"noValueMessage Please use: -qemethod [Reduce|Resolve]")
      case "-z3path" => println(s"noValueMessage Please use: -z3path PATH_TO_z3_FILE")
      case "-tool" => println(s"noValueMessage Please use: -tool mathematica|wolframengine|z3")
      case "-grade" =>
        println(s"noValueMessage Please use: -grade FILENAME.json [-exportanswers [-out DIR]] [-skiponparseerror]")
      case "-proofStatisticsPrinter" =>
        println(s"noValueMessage Please use: -proofStatisticsPrinter [default|arch-nln|arch-hstp]")
      case _ => println(s"[Error] Unknown option $option.")
    }
  }
}
