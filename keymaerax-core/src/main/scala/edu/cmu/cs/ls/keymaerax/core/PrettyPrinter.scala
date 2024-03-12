/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Differential Dynamic Logic expression pretty printing.
 * @author
 *   Andre Platzer
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 * @see
 *   Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015.
 *   [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
 * @see
 *   Andre Platzer. [[https://doi.org/10.1109/LICS.2012.64 The complete proof theory of hybrid systems]]. ACM/IEEE
 *   Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012
 * @note
 *   Code Review 2020-02-17
 */
package edu.cmu.cs.ls.keymaerax.core

/**
 * A pretty printer for differential dynamic logic is an injective function from Expressions to Strings. This object
 * manages the default pretty printer that KeYmaera X uses in [[Expression.prettyString]].
 * @author
 *   Andre Platzer
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.parser.PrettyPrinter]]
 * @see
 *   [[Expression.prettyString]]
 */
object PrettyPrinter extends (Expression => String) {

  /** Pretty-print the given expression using printer() */
  def apply(expr: Expression): String = printer(expr)

  /**
   * A pretty printer for differential dynamic logic is a deterministic, injective function from Expressions to Strings.
   * @ensures
   *   `PrettyPrinter(e1)==PrettyPrinter(e2) => e1==e2`
   */
  type PrettyPrinter = (Expression => String)

  /* @note mutable state for switching out default pretty printers, which defaults to just printing class names as does super.toString */
  private[this] var pp: PrettyPrinter = (e => e.getClass.getName)

  /**
   * The pretty printer that is presently used per default by all [[Expression]] subtypes.
   * @see
   *   [[Expression.prettyString]]
   */
  def printer: PrettyPrinter = pp

  /**
   * Set a new pretty printer to be used by all [[Expression]] types from now on.
   * @param printer
   *   the (deterministic, injective) pretty-printer to use in KeYmaera X from now on.
   * @requires
   *   `printer(e1)==printer(e2) => e1==e2`
   */
  def setPrinter(printer: PrettyPrinter): Unit = { pp = printer }
}
