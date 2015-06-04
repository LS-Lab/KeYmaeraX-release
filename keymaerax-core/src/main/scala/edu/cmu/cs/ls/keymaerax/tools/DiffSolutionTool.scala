package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Tool for computing the symbolic solution of a differential equation system.
 * @author smitsch
 */
trait DiffSolutionTool {
  /**
   * Computes the symbolic solution of a differential equation in normal form.
   * @param diffSys The system of differential equations of the form x' = theta & H.
   * @param diffArg The name of the differential argument (dx/d diffArg = theta).
   * @param iv The initial values per derivative.
   * @return The solution if found; None otherwise
   */
  def diffSol(diffSys: DifferentialProgram, diffArg: Variable, iv: Map[Variable, Function]): Option[Formula]
}
