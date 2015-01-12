package edu.cmu.cs.ls.keymaera.tools

import edu.cmu.cs.ls.keymaera.core._

/**
 * Tool for computing the symbolic solution of a differential equation system.
 * @author smitsch
 */
trait DiffSolutionTool {
  /**
   * Computes the symbolic solution of a differential equation in normal form.
   * @param diffSys The system of differential equations of the form x' = theta & H.
   * @param diffArg The name of the differential argument (dx/d diffArg = theta).
   * @return The solution if found; None otherwise
   */
  def diffSol(diffSys: ContEvolveProgram, diffArg: Variable): Option[Formula]

  /**
   * Computes the symbolic solution of a differential equation in normal form.
   * @param diffEq The differential equation of the form x' = theta & H.
   * @param diffArg The name of the differential argument (dx/d diffArg = theta).
   * @return The solution if found; None otherwise
   */
  def diffSol(diffEq: NFContEvolve, diffArg: Variable): Option[Formula]

  /**
   * Computes the symbolic solution of a system of differential equations.
   * @param diffSys The system of differential equations.
   * @param diffArg The name of the differential argument (dx/d diffArg = theta).
   * @return The solution if found; None otherwise
   */
  def diffSol(diffSys: ContEvolve, diffArg: Variable): Option[Formula]
}