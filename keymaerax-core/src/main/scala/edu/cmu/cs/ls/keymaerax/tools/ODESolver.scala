/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core.{Formula, Function, Variable, DifferentialProgram}

/**
 * Created by nfulton on 4/14/15.
 * @author nfulton
 */
class ODESolver extends DiffSolutionTool {
  /**
   * Computes the symbolic solution of a differential equation in normal form.
   * @param diffSys The system of differential equations of the form x' = theta & H.
   * @param diffArg The name of the differential argument (dx/d diffArg = theta).
   * @param iv The initial values per derivative.
   * @return The solution if found; None otherwise
   */
  override def diffSol(diffSys: DifferentialProgram, diffArg: Variable, iv: Map[Variable, Function]): Option[Formula] = ???
}
