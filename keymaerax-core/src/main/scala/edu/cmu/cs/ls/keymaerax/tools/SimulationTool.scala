/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core.{Formula, NamedSymbol, Number}
import edu.cmu.cs.ls.keymaerax.tools.SimulationTool.{SimRun, SimState, Simulation}

object SimulationTool {
  type SimState = Map[NamedSymbol, Number]
  type SimRun = List[SimState]
  type Simulation = List[SimRun]
}

/**
 * Simulation tool.
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.ToolProvider]]
 */
trait SimulationTool {
  /**
   * Returns a list of simulated states, where consecutive states in the list satisfy 'stateRelation'. The state
   * relation is a modality-free first-order formula. The simulation starts in a state where initial holds (first-order
   * formula).
   * @param initial A first-order formula describing the initial state.
   * @param stateRelation A first-order formula describing the relation between consecutive states. The relationship
   *                      is by name convention: postfix 'pre': prior state; no postfix: posterior state.
   * @param steps The length of the simulation run (i.e., number of states).
   * @param n The number of simulations (different initial states) to create.
   * @return 'n' lists (length 'steps') of simulated states.
   */
  def simulate(initial: Formula, stateRelation: Formula, steps: Int = 10, n: Int = 1): Simulation

  /**
   * Returns a list of simulated states, where consecutive states in the list satisfy 'stateRelation'. The state
   * relation is a modality-free first-order formula. The simulation starts in the specified initial state.
   * @param initial The initial state: concrete values .
   * @param stateRelation A first-order formula describing the relation between consecutive states. The relationship
   *                      is by name convention: postfix 'pre': prior state; no postfix: posterior state.
   * @param steps The length of the simulation run (i.e., number of states).
   * @return A list (length 'steps') of simulated states.
   */
  def simulateRun(initial: SimState, stateRelation: Formula, steps: Int = 10): SimRun
}
