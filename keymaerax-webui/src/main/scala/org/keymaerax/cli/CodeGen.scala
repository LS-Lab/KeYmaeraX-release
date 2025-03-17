/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.cli

import org.keymaerax.Logging
import org.keymaerax.btactics.*
import org.keymaerax.codegen.{CGenerator, CMonitorGenerator, CodeGenerator}
import org.keymaerax.core.{BaseVariable, Equiv, Formula, Imply, StaticSemantics, True}
import org.keymaerax.infrastruct.Augmentors.*
import org.keymaerax.infrastruct.FormulaTools
import org.keymaerax.parser.{ArchiveParser, ParsedArchiveEntry}

import java.io.PrintWriter
import java.nio.file.Path

/** Code generator command-line interface. */
object CodeGen extends Logging {
  def getExtension(path: Path): Option[String] = {
    val name = path.getFileName.toString
    val i = name.lastIndexOf('.')
    if (i < 0) return None
    Some(name.substring(i + 1))
  }

  def removeExtension(path: Path): Path = {
    val name = path.getFileName.toString
    val i = name.lastIndexOf('.')
    if (i < 0) return path
    val nameWithoutExt = name.substring(0, i)
    path.resolveSibling(nameWithoutExt)
  }

  def addExtension(path: Path, ext: String): Path = {
    val name = path.getFileName.toString
    val nameWithExt = s"$name.$ext"
    path.resolveSibling(nameWithExt)
  }

  def changeExtension(path: Path, ext: String): Path = addExtension(removeExtension(path), ext)

  /**
   * Code generator.
   *
   * @param in Input archive file, can be of the form file.kyx#entry
   * @param out Output file (default: input file name with .c suffix)
   * @param quantitative Generate a quantitative instead of a boolean monitor
   * @param interval Use interval arithmetic instead of floating point arithmetic
   */
  def codegen(
      in: String,
      out: Option[String],
      quantitative: Boolean,
      interval: Boolean,
      vars: Option[Set[BaseVariable]],
      args: Seq[String],
  ): Unit = {
    val inputFile = if (in.contains("#")) Path.of(in.substring(0, in.lastIndexOf("#"))) else Path.of(in)

    val inputFormulas = ArchiveParser.parseFromFile(in)
    var outputFile = changeExtension(inputFile, "c")
    for (out <- out) outputFile = Path.of(out)

    val head = EvidencePrinter.stampHead(args)
    val written = inputFormulas.map(e => {
      val outputFileName =
        if (inputFormulas.size <= 1) outputFile.toString
        else {
          var result = outputFile
          result = addExtension(result, e.name.replaceAll("\\s", "_"))
          for (ext <- getExtension(outputFile)) result = addExtension(result, ext)
          result.toString
        }
      if (quantitative) codegenQuantitative(e, outputFileName, head, vars)
      else codegen(e, interval, outputFileName, head, vars)
      outputFileName
    })
    logger.info(s"Generated\n${written.mkString("\n  ")}")
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
      logger.error(
        """Cannot yet augment compiled code with interval arithmetic to guard
          |against floating-point roundoff errors (use -nointerval instead)"""".stripMargin
      )

      logger.error("Interval arithmetic: unfinished")
      // @todo wipe out output file PrintWriter above has already emptied the output file
      // @todo pw.close()
      KeymaeraxCore.exit(-1)
      // TODO what to do when proof cannot be checked?
    } else {
      logger.info(
        """Interval arithmetic: Skipped interval arithmetic generation
          |(use -interval to guard against floating-point roundoff errors)""".stripMargin
      )
    }

    val inputFormula = entry.model.asInstanceOf[Formula]
    if (!inputFormula.isFOL) {
      logger.error(
        "Input is not an arithmetic formula; please use option '-modelplex' first to obtain a monitor formula"
      )
      KeymaeraxCore.exit(-1)
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
    logger.debug(s"[codegen time ${System.currentTimeMillis() - codegenStart} ms]")
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
      logger.error(
        "Input is not an arithmetic formula; please use option '--modelplex' first to obtain a monitor formula"
      )
      KeymaeraxCore.exit(-1)
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
    val monitorProgProof =
      TactixLibrary.proveBy(reassociatedMonitorFml, ModelPlex.chaseToTests(combineTests = false)(1) * 2)
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
