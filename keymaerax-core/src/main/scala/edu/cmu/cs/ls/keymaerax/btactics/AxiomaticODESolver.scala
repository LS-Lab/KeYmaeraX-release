/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{AntePosition, BelleExpr, Position, SuccPosition}
import edu.cmu.cs.ls.keymaerax.core._

/**
  * An Axiomatic ODE solver (second attempt)
  *
  * @see Page 25 in http://arxiv.org/abs/1503.01981 for a high-level sketch.
  * @author Nathan Fulton
  */
object AxiomaticODESolver {
  import TacticFactory._
  import Augmentors._

  val axiomaticSolve = "axiomaticSolve" by ((pos:Position, s:Sequent) => {
    Idioms.nil
  })

  //region Setup time variable

  val setupTimeVar = "setupTimeVar" by((pos: Position, s:Sequent) => {
    s(pos) match {
      case x:DifferentialProgram if timeVar(x).isEmpty => //ok
      case x:ODESystem if timeVar(x).isEmpty => //ok
      case _ => throw AxiomaticODESolverExn(s"setupTimeVar should only be called on differential programs without an existing time variable but found ${s(pos)} of type ${s(pos).getClass}.")
    }

    val modalityPos =
      if(pos.isAnte) AntePosition(pos.checkAnte.top, pos.inExpr.parent)
      else SuccPosition(pos.checkSucc.top, pos.inExpr.parent)
    if(!s(modalityPos).isInstanceOf[Modal])
      throw AxiomaticODESolverExn("Parent position of setupTimeVar should be a modality.")

    val t = TacticHelper.freshNamedSymbol(Variable("kyxtime"), s)

    HilbertCalculus.DG(t, Number(0), Number(1))(modalityPos)
  })

  /** Returns the unique time variable in diffProgram, or None if no time variable can be found.
    * @throws AxiomaticODESolverExn whenever diffProgram contains more than one time variable */
  private def timeVar(diffProgram: DifferentialProgram) : Option[Variable] = diffProgram match {
    case x:AtomicODE if isOne(x.e)  => Some(x.xp.x)
    case x:AtomicODE if !isOne(x.e) => None
    case x:DifferentialProgramConst => None
    case x:DifferentialProduct      => (timeVar(x.left), timeVar(x.right)) match {
      case (None, None)       => None
      case (None, Some(x))    => Some(x)
      case (Some(x), None)    => Some(x)
      case (Some(x), Some(y)) => throw AxiomaticODESolverExn(s"Expected one time variable but found many (${x} and ${y}) in ${diffProgram}")
    }
  }
  private def timeVar(system: ODESystem): Option[Variable] = timeVar(system.ode)

  private def isOne(t: Term) = t == Number(1) //@todo more robust implementation. E.g. QE.

  //endregion

  /** Exceptions thrown by the axiomatic ODE solver. */
  case class AxiomaticODESolverExn(msg: String) extends Exception(msg)
}

/*
Todo list:
 1. Implement differential ghosts and inverse differential ghosts.
 2. Add t' = 1 if it's not already present
 3. Re-order the ODE so that it's in the correct dependency ordering.
 ...
 */