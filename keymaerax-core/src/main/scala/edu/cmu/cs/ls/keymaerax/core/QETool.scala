/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * @note Code Review: 2015-08-24
 */
package edu.cmu.cs.ls.keymaerax.core

/**
 * Quantifier elimination tool.
 */
trait QETool {
  /**
   * Returns a quantifier-free formula that is equivalent to the specified formula.
   * @param formula The formula whose quantifier-free equivalent is sought.
   * @return An equivalent quantifier-free formula.
   */
  def qe(formula: Formula): Formula

  /**
   * Returns a quantifier-free formula that is equivalent to the specified formula, together with the actual input
   * sent to this tool and the actual output it produced.
   * @param formula The formula whose quantifier-free equivalent is sought.
   * @return An equivalent quantifier-free formula, with tool evidence.
   */
  def qeEvidence(formula: Formula): (Formula, Evidence)
}
