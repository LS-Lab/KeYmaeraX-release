/**
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaera.core

/**
 * Quantifier elimination tool.
 */
trait QETool {
  /**
   * Returns a quantifier-free formula that is equivalent to the specified formula.
   * @param formula The formula.
   * @return An equivalent quantifier-free formula.
   */
  def qe(formula: Formula): Formula

  /**
   * Returns a quantifier-free formula that is equivalent to the specified formula, together with the actual input
   * sent to this tool and the actual output it produced.
   * @param formula The formula.
   * @return An equivalent quantifier-free formula, with tool input and output.
   * @todo rename to quantifiereElimination(Formula): Evidence
   */
  def qeInOut(formula: Formula): (Formula, String, String)
}
