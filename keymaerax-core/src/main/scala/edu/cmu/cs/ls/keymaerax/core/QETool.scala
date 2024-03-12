/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/** @note Code Review: 2020-02-17 */
package edu.cmu.cs.ls.keymaerax.core

/** Interface to quantifier elimination tools. */
trait QETool {

  /**
   * Returns a quantifier-free formula that is equivalent to the specified formula.
   * @param formula
   *   The formula whose quantifier-free equivalent is sought.
   * @return
   *   An equivalent quantifier-free formula.
   * @requires
   *   formula is in first-order real arithmetic
   * @ensures
   *   \result is equivalent to formula
   * @ensures
   *   `\result is quantifier-free
   */
  def quantifierElimination(formula: Formula): Formula
}
