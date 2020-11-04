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
import edu.cmu.cs.ls.keymaerax.tools._

/**
  * A QE tool implementation using the provided link to Mathematica/Wolfram Engine.
  * @param link The link to Mathematica/Wolfram Engine.
  * @author Nathan Fulton
  * @author Stefan Mitsch
  */
class MathematicaQETool(val link: MathematicaCommandRunner) extends QETool {

  /** @inheritdoc */
  override def quantifierElimination(formula: Formula): Formula = {
    val f = try {
      KeYmaeraToMathematica(formula)
    } catch {
      case ex: ConversionException => throw ex
      case ex: Throwable => throw ConversionException("Error converting to Mathematica: " + formula.prettyString, ex)
    }
    val method = Configuration.getString(Configuration.Keys.MATHEMATICA_QE_METHOD).getOrElse("Reduce") match {
      case "Reduce" => MathematicaOpSpec.reduce
      case "Resolve" => MathematicaOpSpec.resolve
      case m => throw ToolCommunicationException("Unknown Mathematica QE method '" + m + "'. Please configure either 'Reduce' or 'Resolve'.")
    }
    val input = method(f, MathematicaOpSpec.list(), MathematicaOpSpec.reals.op)
    try {
      val (_, result) = link.run(input, MathematicaToKeYmaera)
      result match {
        case resultFormula: Formula => resultFormula
        case _ => throw ConversionException("Expected a formula from Reduce call but got a non-formula expression.")
      }
    } finally { input.dispose() }
  }

}
