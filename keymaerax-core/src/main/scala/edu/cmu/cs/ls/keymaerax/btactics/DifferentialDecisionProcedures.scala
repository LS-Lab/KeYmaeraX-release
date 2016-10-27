/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{DependentPositionTactic, Position}
import edu.cmu.cs.ls.keymaerax.core.Sequent
import TacticFactory._

/**
  * Decision procedures for various classes of differential equations.
  *
  * @author Nathan Fulton
  */
object DifferentialDecisionProcedures {

  /** Runs all available decision procedures. */
  def apply() : DependentPositionTactic =  "DifferentialDecisionProcedures" by ((pos: Position, seq: Sequent) => {
    linearSystem(pos)
  })

  lazy val linearSystem: DependentPositionTactic = AxiomaticODESolver.apply()

  lazy val ricattiEquation: DependentPositionTactic = ???

  /** A decision procedure for a single exponential equation. */
  lazy val exponentialEquation: DependentPositionTactic = ???

  /** A decision proceudre for a system of Ricatti equations together with an independent exponential equation
    * @author Nathan Fulton */
  lazy val ricattiWithExponentials: DependentPositionTactic = ???
}


/**
  * Decision procedure for a single Ricatti equation.
  * @author Nathan Fulton */
object RicattiEquation {

}

/** Decision procedure for a system of Ricatti differential equations.
  * @author Nathan Fulton */
object RicattiSystem {

}

