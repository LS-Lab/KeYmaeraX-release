/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-06-01 (QETool parts and its dependencies only)
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable

/**
 * A QE tool implementation using Mathematica over the JLink interface.
 * @author Nathan Fulton
 * @author Stefan Mitsch
 */
class MathematicaQETool extends JLinkMathematicaLink(KeYmaeraToMathematica, MathematicaToKeYmaera) with QETool {

  def qeEvidence(f : Formula) : (Formula, Evidence) = {
    val input = new MExpr(MathematicaSymbols.REDUCE,
      Array(k2m(f), new MExpr(MathematicaSymbols.LIST, new Array[MExpr](0)), MathematicaSymbols.REALS))
    val (output, result) = run(input)
    result match {
      case f : Formula =>
        if (DEBUG) println("Mathematica QE result: " + f.prettyString)
        (f, new ToolEvidence(immutable.Map("input" -> input.toString, "output" -> output)))
      case _ => throw new ToolException("Expected a formula from Reduce call but got a non-formula expression.")
    }
  }

}