/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Differential Dynamic Logic pretty-printer for concrete KeYmaera X notation.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Pretty-Printer interface for KeYmaera X.
 * @author aplatzer
 */
trait PrettyPrinter extends (Expression => String) {

  /**
   * Pretty-print expression to a string
   * @ensures parser(\result) == expr
   */
  def apply(expr: Expression): String

  /** The corresponding full-form pretty printer with full parentheses. */
  def fullPrinter: (Expression => String)

  /** A parser that can read the input that this pretty-printer produces */
  def parser: Parser

}
