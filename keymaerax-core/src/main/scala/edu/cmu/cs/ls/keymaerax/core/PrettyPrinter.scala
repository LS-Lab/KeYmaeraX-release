/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Differential Dynamic Logic expression pretty printing.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @see "Andre Platzer. The complete proof theory of hybrid systems. ACM/IEEE Symposium on Logic in Computer Science, LICS 2012, June 25–28, 2012, Dubrovnik, Croatia, pages 541-550. IEEE 2012"
 */
package edu.cmu.cs.ls.keymaerax.core

/**
 * A pretty printer for differential dynamic logic is a function from Expressions to Strings.
 * @author aplatzer
 */
object PrettyPrinter {
  /**
   * A pretty printer for differential dynamic logic is a function from Expressions to Strings.
   */
  type PrettyPrinter = (Expression => String)

  private var pp: PrettyPrinter = (e => e.canonicalString)

  //@todo move this initialization outside the core
  setPrinter(edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter)

  def printer: PrettyPrinter = pp

  /**
   * Set a new pretty printer to be used from now on.
   * @param printer
   */
  def setPrinter(printer: PrettyPrinter) = {pp = printer}
}
