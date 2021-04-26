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
  /** QE options, see [[https://reference.wolfram.com/language/tutorial/RealPolynomialSystems.html]] (InequalitySolvingOptions). */
  private val qeOptions = Configuration.getMap(Configuration.Keys.MATHEMATICA_QE_OPTIONS).map({ case (k, v) =>
    MathematicaOpSpec.rule(MathematicaOpSpec.string(k), v match {
      case "true" | "false" => MathematicaOpSpec.bool(v.toBoolean)
      case _ => MathematicaOpSpec.string(v)
    })
  }).toList

  /** QE method, one of `Resolve` or `Reduce`. */
  private val qeMethod = Configuration.getString(Configuration.Keys.MATHEMATICA_QE_METHOD).getOrElse("Reduce")

  /** @inheritdoc */
  override def quantifierElimination(formula: Formula): Formula = {
    val f = try {
      KeYmaeraToMathematica(formula)
    } catch {
      case ex: ConversionException => throw ex
      case ex: Throwable => throw ConversionException("Error converting to Mathematica: " + formula.prettyString, ex)
    }
    val doQE = qeMethod match {
      case "Reduce" => (f: MathematicaConversion.MExpr) => MathematicaOpSpec.reduce(f, MathematicaOpSpec.list(), MathematicaOpSpec.reals.op)
      case "Resolve" => (f: MathematicaConversion.MExpr) => MathematicaOpSpec.resolve(f, MathematicaOpSpec.reals.op)
      case m => throw ToolCommunicationException("Unknown Mathematica QE method '" + m + "'. Please configure either 'Reduce' or 'Resolve'.")
    }
    val input =
      if (qeOptions.nonEmpty) MathematicaOpSpec.compoundExpr(
        MathematicaOpSpec(MathematicaOpSpec.symbol("SetSystemOptions"))(
          MathematicaOpSpec.rule(
            MathematicaOpSpec.string("InequalitySolvingOptions"),
            MathematicaOpSpec.list(qeOptions:_*)) :: Nil
        ),
        doQE(f)
      )
      else doQE(f)
    try {
      val (_, result) = link.run(input, MathematicaToKeYmaera)
      result match {
        case resultFormula: Formula => resultFormula
        case _ => throw ConversionException("Expected a formula from Reduce call but got a non-formula expression.")
      }
    } finally { input.dispose() }
  }

}
