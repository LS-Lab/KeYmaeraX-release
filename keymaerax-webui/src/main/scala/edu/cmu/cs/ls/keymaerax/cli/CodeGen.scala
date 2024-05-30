/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.cli.KeYmaeraX.exit
import edu.cmu.cs.ls.keymaerax.codegen.{CGenerator, CMonitorGenerator, CodeGenerator}
import edu.cmu.cs.ls.keymaerax.core.{BaseVariable, Equiv, Formula, Imply, StaticSemantics, True}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.FormulaTools
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, ParsedArchiveEntry}

import java.io.PrintWriter
import scala.reflect.io.File

/** Code generator command-line interface. */
object CodeGen {

  /**
   * Code generator.
   * @param options
   *   Options to steer the code generator:
   *   - 'in (mandatory) input archive file, can be of the form file.kyx#entry
   *   - 'out (optional) output file (default: 'in.c)
   *   - 'vars (optional)
   *   - 'interval (optional) Whether to use interval arithmetic or floating point arithmetic (default: interval)
   *   - 'quantitative (optional) Whether to generate a quantitative or boolean monitor (default: true)
   * @param usage
   *   Usage information to print on wrong usage.
   */
  def codegen(options: Options, usage: String): Unit = {
    require(options.in.isDefined, usage)

    val inputFileName = options.in.get
    val inputFile =
      if (inputFileName.contains("#")) File(inputFileName.substring(0, inputFileName.lastIndexOf("#")))
      else File(inputFileName)

    val inputFormulas = ArchiveParser.parseFromFile(inputFileName)
    var outputFile = inputFile.changeExtension("c")
    if (options.out.isDefined) outputFile = File(options.out.get)

    val vars: Option[Set[BaseVariable]] = options.vars.map(_.toSet)

    val interval = options.interval.getOrElse(true)
    val head = EvidencePrinter.stampHead(options)
    val quantitative = options.quantitative.getOrElse(false)
    val written = inputFormulas.map(e => {
      val outputFileName =
        if (inputFormulas.size <= 1) outputFile.toString()
        else {
          val ext = outputFile.extension
          outputFile.addExtension(e.name.replaceAll("\\s", "_")).addExtension(ext).toString()
        }
      if (quantitative) codegenQuantitative(e, outputFileName, head, vars)
      else codegen(e, interval, outputFileName, head, vars)
      outputFileName
    })
    println("Generated\n  " + written.mkString("\n  "))
  }

  def codegen(
      entry: ParsedArchiveEntry,
      interval: Boolean,
      outputFileName: String,
      head: String,
      vars: Option[Set[BaseVariable]],
  ): Unit = {
    if (interval) {
      // @todo check that when assuming the output formula as an additional untrusted lemma, the Provable isProved.
      System
        .err
        .println(
          "Cannot yet augment compiled code with interval arithmetic to guard against floating-point roundoff errors\n(use -nointerval instead)"
        )

      println("Interval arithmetic: unfinished")
      System.err.println("Interval arithmetic: unfinished")
      // @todo wipe out output file PrintWriter above has already emptied the output file
      // @todo pw.close()
      exit(-1)
      // TODO what to do when proof cannot be checked?
    } else {
      println(
        "Interval arithmetic: Skipped interval arithmetic generation\n(use -interval to guard against floating-point roundoff errors)"
      )
    }

    val inputFormula = entry.model.asInstanceOf[Formula]
    if (!inputFormula.isFOL) {
      println("Input is not an arithmetic formula; please use option '-modelplex' first to obtain a monitor formula")
      exit(-1)
    }

    // @note codegen in C format only regardless of file extension
    val theVars = vars match {
      case Some(v) => v
      case None => StaticSemantics
          .vars(inputFormula)
          .symbols
          .filter(_.isInstanceOf[BaseVariable])
          .map(_.asInstanceOf[BaseVariable])
    }

    val codegenStart = System.currentTimeMillis()
    // @todo input variables (nondeterministically assigned in original program)
    val output = (
      new CGenerator(new CMonitorGenerator(Symbol("resist"), entry.defs), True, entry.defs)
    )(inputFormula, theVars, Set(), outputFileName)
    Console.println("[codegen time " + (System.currentTimeMillis() - codegenStart) + "ms]")
    val pw = new PrintWriter(outputFileName)
    pw.write(head)
    pw.write("/* @evidence: print of CGenerator of input */\n\n")
    pw.write(output._1 + "\n" + output._2)
    pw.close()
  }

  def codegenQuantitative(
      entry: ParsedArchiveEntry,
      outputFileName: String,
      head: String,
      vars: Option[Set[BaseVariable]],
  ): Unit = {
    val monitorFml = entry.model.asInstanceOf[Formula]

    if (!monitorFml.isFOL) {
      println("Input is not an arithmetic formula; please use option '-modelplex' first to obtain a monitor formula")
      exit(-1)
    }

    val monitorStateVars = vars match {
      case Some(v) => v
      case None =>
        StaticSemantics.vars(entry.model).symbols.filter(_.isInstanceOf[BaseVariable]).map(_.asInstanceOf[BaseVariable])
    }

    val reassociatedMonitorFml = FormulaTools.reassociate(monitorFml)
    val reassociation = TactixLibrary.proveBy(Equiv(monitorFml, reassociatedMonitorFml), TactixLibrary.prop)
    assert(
      reassociation.isProved,
      "Reassociated formula incorrectly: failed to prove\n" + reassociation.conclusion.prettyString,
    )
    val monitorProgProof = TactixLibrary
      .proveBy(reassociatedMonitorFml, ModelPlex.chaseToTests(combineTests = false)(1) * 2)
    assert(
      monitorProgProof.subgoals.size == 1,
      "Converted to tests incorrectly: expected a single goal but got\n" + monitorProgProof.prettyString,
    )
    val Imply(True, monitorProg) = monitorProgProof.subgoals.head.toFormula
    val inputs = CodeGenerator.getInputs(monitorProg)
    val monitorCode = (
      new CGenerator(new CMonitorGenerator(Symbol("resist"), entry.defs), True, entry.defs)
    )(monitorProg, monitorStateVars, inputs, "Monitor")

    val pw = new PrintWriter(outputFileName)
    pw.write(head)
    pw.write("/* @evidence: print of CGenerator of input */\n\n")
    pw.write(monitorCode._1 + "\n" + monitorCode._2)
    pw.close()
  }
}
