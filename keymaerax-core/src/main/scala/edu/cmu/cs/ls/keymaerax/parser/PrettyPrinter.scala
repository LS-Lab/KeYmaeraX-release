/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Differential Dynamic Logic pretty-printer for concrete KeYmaera X notation.
 * @author Andre Platzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Pretty-Printer interface for KeYmaera X.
 * A pretty-printer formats the [[edu.cmu.cs.ls.keymaerax.core.Expression differential dynamic logic expression data structure]]
 * as human readable concrete syntax.
 * A pretty-printer is essentially a function from differential dynamic logic [[edu.cmu.cs.ls.keymaerax.core.Expression expressions]] to strings.
 * {{{
 *     PrettyPrinter: Expression => String
 * }}}
 * @author Andre Platzer
 * @see [[edu.cmu.cs.ls.keymaerax.core.PrettyPrinter]]
 */
trait PrettyPrinter extends (Expression => String) {

  /**
   * Pretty-print expression to a string.
   * @ensures parser(\result) == expr
   */
  def apply(expr: Expression): String

  /**
   * Pretty-print sequent to a string.
   * @ensures parser(\result) == expr
   */
  def apply(seq: Sequent): String

  /**
   * The corresponding full-form pretty printer producing full parentheses.
   * @ensures parser(fullPrinter(expr)) == expr
   */
  def fullPrinter: (Expression => String)

  /** A parser that can read the input that this pretty-printer produces */
  def parser: Parser

}
