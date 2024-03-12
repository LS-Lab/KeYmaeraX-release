/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Differential Dynamic Logic pretty-printer for concrete KeYmaera X notation.
 * @author
 *   Andre Platzer
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 * @note
 *   Code Review 2020-02-14
 */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Pretty-Printer interface for KeYmaera X. A pretty-printer is an injective function formatting the
 * [[edu.cmu.cs.ls.keymaerax.core.Expression differential dynamic logic expression data structure]] as human-readable
 * concrete syntax. A pretty-printer is an injective function from differential dynamic logic
 * [[edu.cmu.cs.ls.keymaerax.core.Expression expressions]] to strings.
 * {{{
 *     PrettyPrinter: Expression => String
 * }}}
 * @author
 *   Andre Platzer
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.core.PrettyPrinter]]
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 */
trait PrettyPrinter extends (Expression => String) {

  /**
   * Pretty-print expression to a string.
   * @ensures
   *   parser(\result) == expr
   * @ensures
   *   apply(e1)==apply(e2) => e1==e2
   */
  def apply(expr: Expression): String

  /**
   * Pretty-print sequent to a string.
   * @ensures
   *   parser(\result) == expr
   * @ensures
   *   apply(seq1)==apply(seq2) => seq1==seq2
   */
  def apply(seq: Sequent): String

  /**
   * The corresponding full-form pretty printer producing full parentheses.
   * @ensures
   *   parser(fullPrinter(expr)) == expr
   * @ensures
   *   fullPrinter(e1)==fullPrinter(e2) => e1==e2
   */
  val fullPrinter: (Expression => String)

  /** A parser that can read the input that this pretty-printer produces */
  val parser: Parser

}
