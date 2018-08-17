/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-06-01 (QETool parts and its dependencies only)
  */
package edu.cmu.cs.ls.keymaerax.tools

import com.wolfram.jlink.Expr
import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.FormulaTools
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.MathematicaConversion.{KExpr, MExpr}
import org.apache.logging.log4j.scala.Logging

import scala.collection.immutable

/**
 * A QE tool implementation using Mathematica over the JLink interface.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class MathematicaQETool(override val link: MathematicaLink)
  extends BaseKeYmaeraMathematicaBridge[KExpr](link, KeYmaeraToMathematica, MathematicaToKeYmaera) with QETool with Logging {

  /** Adds assertions of form {{{t \[Element] Reals}}} for each term in mustBeReal. */
  private def conjunctDomainAssumptions(originalInput: MExpr, mustBeReal: List[Term]) = {
    val domainAssumptions = mustBeReal.map(k2m).map(mTerm =>
      //term \in Reals
      new Expr(new Expr(Expr.SYMBOL, "Element"), (mTerm :: new Expr(Expr.SYMBOL, "Reals") :: Nil).toArray)
    )
    new Expr(new Expr(Expr.SYMBOL, "And"), (domainAssumptions :+ originalInput).toArray)
  }

  def qeEvidence(originalFormula: Formula): (Formula, Evidence) = {
    val f = {
      val mustBeReals = FormulaTools.unnaturalPowers(originalFormula)
      val convertedFormula = k2m(originalFormula)
      conjunctDomainAssumptions(convertedFormula, mustBeReals)
    }
    val method = Configuration.getOption(Configuration.Keys.MATHEMATICA_QE_METHOD).getOrElse("Reduce") match {
      case "Reduce" => MathematicaSymbols.REDUCE
      case "Resolve" => MathematicaSymbols.RESOLVE
      case m => throw new IllegalStateException("Unknown Mathematica QE method '" + m + "'. Please configure either 'Reduce' or 'Resolve'.")
    }
    val input = new MExpr(method,
      Array(f, new MExpr(MathematicaSymbols.LIST, new Array[MExpr](0)), MathematicaSymbols.REALS))
    try {
      val (output, result) = run(input)
      result match {
        case resultingQeFormula: Formula =>
          logger.debug(s"Mathematica QE result from input ${originalFormula.prettyString}: " + resultingQeFormula.prettyString)
          (resultingQeFormula, ToolEvidence(immutable.List("input" -> input.toString, "output" -> output)))
        case _ => throw ToolException("Expected a formula from Reduce call but got a non-formula expression.")
      }
    } finally { input.dispose() }
  }

}
