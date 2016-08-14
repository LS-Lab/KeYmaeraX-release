/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * @note Code Review: 2015-08-24
 */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core.{Formula, NamedSymbol, Term}

/**
 * Quantifier elimination tool.
 */
trait CounterExampleTool {
  /**
   * Returns a counterexample for the specified formula.
   * @param formula The formula.
   * @return A counterexample, if found. None otherwise.
   */
  def findCounterExample(formula: Formula): Option[Map[NamedSymbol, Term]]
}
