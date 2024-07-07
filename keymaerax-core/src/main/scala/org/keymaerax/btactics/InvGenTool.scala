/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import org.keymaerax.core.{Expression, Formula, NamedSymbol, ODESystem}

import scala.collection.immutable.Seq

/**
 * Continuous invariant generation tool.
 * @see
 *   [[org.keymaerax.btactics.ToolProvider]]
 */
trait InvGenTool {

  /**
   * Returns a continuous invariant for a safety problem sent to the tool.
   * @param ode
   *   The differential equation for which to generate a continuous invariants.
   * @param assumptions
   *   Assumptions on the initial state of the ODE.
   * @param postCond
   *   What to prove from the invariants.
   * @return
   *   A sequence of continuous invariants, each to be proved with a diffcut chain (left=invariant, right=candidate).
   */
  def invgen(
      ode: ODESystem,
      assumptions: Seq[Formula],
      postCond: Formula,
  ): Seq[Either[Seq[(Formula, String)], Seq[(Formula, String)]]]

  /** Fast check whether or not `inv` is worth proving to be an invariant of `ode`. */
  def lzzCheck(ode: ODESystem, inv: Formula): Boolean

  /** Finds counterexamples to an ODE safety conjecture. */
  def refuteODE(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): Option[Map[NamedSymbol, Expression]]

  /**
   * Returns the sufficient/necessary condition for postCond to be invariant (left of pair) also returns necessary
   * conditions for the safety question to be true at all with those assumptions (right of pair) In either case, all
   * formulas in the returned list must be valid
   */
  def genODECond(ode: ODESystem, assumptions: Seq[Formula], postCond: Formula): (List[Formula], List[Formula])
}
