/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Tool for computing symbolic derivatives (oracle for tactics).
 * @author Andre Platzer
 */
trait DerivativeTool {
  /**
   * Computes the symbolic partial derivative of the given term by `v`.
    * {{{
    *   d(term)
    *   ------
    *     dv
    * }}}
   * @param term The term whose partial derivative is sought.
   * @param v The variable to derive by.
   * @return The partial derivative of `term` by `v`.
   */
  def deriveBy(term: Term, v: Variable): Term
}
