/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * @note Code Review: 2016-08-17
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
  def quantifierElimination(formula: Formula): Formula
}
