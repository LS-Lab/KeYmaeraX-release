/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core.{Formula, ODESystem}

import scala.collection.immutable.Seq

/**
  * Continuous invariant generation tool.
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.ToolProvider]]
  */
trait InvGenTool {
  /**
    * Returns a continuous invariant for a safety problem sent to the tool.
    * @param ode The differential equation for which to generate a continuous invariants.
    * @param assumptions Assumptions on the initial state of the ODE.
    * @param postCond What to prove from the invariants.
    * @return A sequence of continuous invariants, each to be proved with a diffcut chain (left=invariant, right=candidate).
    */
  def invgen(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): Seq[Either[Seq[Formula],Seq[Formula]]]

  /** Fast check whether or not `inv` is worth proving to be an invariant of `ode`. */
  def lzzCheck(ode: ODESystem, inv: Formula): Boolean
}

