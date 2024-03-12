/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.DependentPositionTactic
import edu.cmu.cs.ls.keymaerax.core.Sequent
import TacticFactory._
import edu.cmu.cs.ls.keymaerax.infrastruct.Position

/**
 * Decision procedures for various classes of differential equations.
 *
 * @author
 *   Nathan Fulton
 */
object DifferentialDecisionProcedures {

  /** Runs all available decision procedures. */
  // was "DifferentialDecisionProcedures"
  def apply(): DependentPositionTactic = anon((pos: Position, seq: Sequent) => { linearSystem(pos) })

  lazy val linearSystem: DependentPositionTactic = AxiomaticODESolver.apply()

  lazy val ricattiEquation: DependentPositionTactic = ???

  /** A decision procedure for a single exponential equation. */
  lazy val exponentialEquation: DependentPositionTactic = ???

  /**
   * A decision procedure for a system of Ricatti equations together with an independent exponential equation
   * @author
   *   Nathan Fulton
   */
  lazy val ricattiWithExponentials: DependentPositionTactic = ???
}

/**
 * Decision procedure for a single Ricatti equation.
 * @author
 *   Nathan Fulton
 */
object RicattiEquation {}

/**
 * Decision procedure for a system of Ricatti differential equations.
 * @author
 *   Nathan Fulton
 */
object RicattiSystem {}
