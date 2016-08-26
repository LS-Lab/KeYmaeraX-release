/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Tool for algebraic computations.
 * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.ToolProvider]]
 */
trait AlgebraTool {
  /**
   * Computes the quotient and remainder of `term` divided by `div`.
    * @example{{{
    *           quotientRemainder(6*x^2+4*x+8, 2*x, x) == (3*x+2, 8)
    * }}}
   */
  def quotientRemainder(term: Term, div: Term, v: Variable): (Term, Term)
}
