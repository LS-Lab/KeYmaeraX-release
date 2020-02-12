/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-06-01 (QETool parts and its dependencies only)
  */
package edu.cmu.cs.ls.keymaerax.tools.qe

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.lemma.Evidence
import edu.cmu.cs.ls.keymaerax.tools._
import org.apache.logging.log4j.scala.Logging

import scala.collection.immutable

/**
  * A QE tool implementation using the provided link to Mathematica/Wolfram Engine.
  * @param link The link to Mathematica/Wolfram Engine.
  * @author Nathan Fulton
  * @author Stefan Mitsch
  */
class MathematicaQETool(val link: MathematicaCommandRunner) extends QETool with Logging {

  /** @inheritdoc */
  override def quantifierElimination(formula: Formula) = qeEvidence(formula)._1

  /** @inheritdoc */
  def qeEvidence(originalFormula: Formula): (Formula, Evidence) = {
//    val f = {
//      val mustBeReals = FormulaTools.unnaturalPowers(originalFormula)
//      val mustBeRealsInParentFml = mustBeReals.map({ case (t: Term, p: PosInExpr) =>
//        val parentFormulaPos = FormulaTools.parentFormulaPos(p, originalFormula)
//        originalFormula.sub(parentFormulaPos).get.asInstanceOf[Formula] -> (t -> parentFormulaPos)
//      })
//      new EnsureRealsK2M(originalFormula, mustBeRealsInParentFml.toMap)(originalFormula)
//    }
    val f = KeYmaeraToMathematica(originalFormula)
    val method = Configuration.getOption(Configuration.Keys.MATHEMATICA_QE_METHOD).getOrElse("Reduce") match {
      case "Reduce" => MathematicaOpSpec.reduce
      case "Resolve" => MathematicaOpSpec.resolve
      case m => throw new IllegalStateException("Unknown Mathematica QE method '" + m + "'. Please configure either 'Reduce' or 'Resolve'.")
    }
    val input = method(f, MathematicaOpSpec.list(), MathematicaOpSpec.reals.op)
    try {
      val (output, result) = link.run(input, MathematicaToKeYmaera)
      result match {
        case resultingQeFormula: Formula =>
          logger.debug(s"Mathematica QE result from input ${originalFormula.prettyString}: " + resultingQeFormula.prettyString)
          (resultingQeFormula, ToolEvidence(immutable.List("input" -> input.toString, "output" -> output)))
        case _ => throw ToolException("Expected a formula from Reduce call but got a non-formula expression.")
      }
    } finally { input.dispose() }
  }

}
