/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Tool for computing the solution of an equation system.
 * @author Andre Platzer
 */
trait SolutionTool {
  /**
   * Computes the symbolic solution of an equation system.
   * @param equations The system of equations as a conjunction of equations.
   * @param vars The variables or symbols to solve for.
    *            Within reason, it may also be possible to solve for compound expressions like solve for j(z).
   * @return The solution if found; None otherwise
    *         The solution should be a conjunction of explicit equations for the vars.
    *         Or a disjunction of a conjunction of explicit equations for the vars.
    * @example{{{
    *           solve("z+1=3&x+5=z-1".asFormula, Variable("z")::Variable("x")::Nil) == Some("z=2&x=-4")
    * }}}
   */
  def solve(equations: Formula, vars: List[Expression]): Option[Formula]
}
