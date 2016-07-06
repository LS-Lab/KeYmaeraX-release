/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.Position
import edu.cmu.cs.ls.keymaerax.core._

/**
  * An Axiomatic ODE solver (second attempt)
  *
  * @see Page 25 in http://arxiv.org/abs/1503.01981
  * @author Nathan Fulton
  */
object AxiomaticODESover {
  import TacticFactory._
  val axiomaticSolve = "axiomaticSolve" by ((pos:Position, s:Sequent) => {
    Idioms.nil
  })

  /** Returns the unique time variable in diffProgram, or None if no time variable can be found.
    * @throws AxiomaticODESolverExn whenever diffProgram contains more than one time variable */
  private def timeVar(diffProgram: DifferentialProgram) : Option[Variable] = diffProgram match {
    case x:AtomicODE if isOne(x.e)  => Some(x.xp.x)
    case x:AtomicODE if !isOne(x.e) => None
    case x:DifferentialProgramConst => None
    case x:ODESystem                => timeVar(x.ode)
    case x:DifferentialProduct      => (timeVar(x.left), timeVar(x.right)) match {
      case (None, None)       => None
      case (None, Some(x))    => Some(x)
      case (Some(x), None)    => Some(x)
      case (Some(x), Some(y)) => throw AxiomaticODESolverExn(s"Expected one time variable but found many (${x} and ${y}) in ${diffProgram}")
    }
  }

  private def isOne(t: Term) = t == Number(1) //@todo more robust implementation. E.g. QE.

  /** Exceptions thrown by the axiomatic ODE solver. */
  case class AxiomaticODESolverExn(msg: String) extends Exception(msg)
}