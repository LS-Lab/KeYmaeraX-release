/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Differential Dynamic Logic expression pretty printing.
 * @author Andre Platzer
 * @see
 *   [[org.keymaerax.Bibliography.JarPlatzer17 A complete uniform substitution calculus for differential dynamic logic]]
 * @see [[org.keymaerax.Bibliography.ToclPlatzer15 Differential game logic]]
 * @see [[org.keymaerax.Bibliography.LicsPlatzer12b The complete proof theory of hybrid systems]]
 * @note Code Review 2020-02-17
 */
package org.keymaerax.core

/**
 * A pretty printer for differential dynamic logic is an injective function from Expressions to Strings. This object
 * manages the default pretty printer that KeYmaera X uses in [[Expression.prettyString]].
 * @author Andre Platzer
 * @see [[org.keymaerax.parser.PrettyPrinter]]
 * @see [[Expression.prettyString]]
 */
object PrettyPrinter extends (Expression => String) {

  /** Pretty-print the given expression using printer() */
  def apply(expr: Expression): String = printer(expr)

  /**
   * A pretty printer for differential dynamic logic is a deterministic, injective function from Expressions to Strings.
   * @ensures `PrettyPrinter(e1)==PrettyPrinter(e2) => e1==e2`
   */
  type PrettyPrinter = (Expression => String)

  /* @note mutable state for switching out default pretty printers, which defaults to just printing class names as does super.toString */
  private[this] var pp: PrettyPrinter = (e => e.getClass.getName)

  /**
   * The pretty printer that is presently used per default by all [[Expression]] subtypes.
   * @see [[Expression.prettyString]]
   */
  def printer: PrettyPrinter = pp

  /**
   * Set a new pretty printer to be used by all [[Expression]] types from now on.
   * @param printer the (deterministic, injective) pretty-printer to use in KeYmaera X from now on.
   * @requires `printer(e1)==printer(e2) => e1==e2`
   */
  def setPrinter(printer: PrettyPrinter): Unit = { pp = printer }
}
