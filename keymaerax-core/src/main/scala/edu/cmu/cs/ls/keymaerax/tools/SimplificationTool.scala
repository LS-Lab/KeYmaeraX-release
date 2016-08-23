/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core._

/**
  * Tool for simplifying logical and/or arithmetical expressions.
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.ToolProvider]]
  */
trait SimplificationTool {
  /**
   * Simplifies the given expression `expr`, under the list of assumptions.
   * @param expr The formula or term to simplify.
   * @param assumptions The list of logical formulas whose conjunction is assumed to hold during the simplification.
    *                   The assumptions are allowed to contain additional conjunctions.
   * @return A simplified version of `expr`.
    * @example{{{
    *           simplify("a*x^2+b^2 > a*x^3+b*abs(b)".asFormula, "x>1".asFormula :: "b>0".asFormula::Nil) == "a<0".asFormula
    *           simplify("a*x^2+b^2 > a*x^3+b*abs(b)".asFormula, "x>1 && b>0".asFormula::Nil) == "a<0".asFormula
    * }}}
   */
  def simplify(expr: Expression, assumptions: List[Formula]): Expression
  def simplify(expr: Formula, assumptions: List[Formula]): Formula
  def simplify(expr: Term, assumptions: List[Formula]): Term
}
