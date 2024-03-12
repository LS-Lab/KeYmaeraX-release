/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.btactics.TacticHelper._
import edu.cmu.cs.ls.keymaerax.btactics.ODEInvariance.dot_prod
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._

/** Implements ODE tactics for stability */

object ODEStability {

  // Returns a formula for the v-neighborhood of the origin
  private def neighborhood(v: Term, xs: List[Variable]): Formula = { Less(dot_prod(xs, xs), Times(v, v)) }

  // Returns a formula specifying stability of the origin for the input ODE
  def stabODE(ode: DifferentialProgram): Formula = {
    val eps = TacticHelper.freshNamedSymbol(Variable("eps"), Box(ode, True))
    val del = TacticHelper.freshNamedSymbol(Variable("del"), Box(ode, True))
    val zero = Number(0)

    val odevars = DifferentialProduct
      .listify(ode)
      .map {
        case AtomicODE(xp, _) => xp.x
        case _ => throw new IllegalArgumentException("stability only for concrete ODEs")
      }

    // The inner safety specification
    val inner = Imply(neighborhood(del, odevars), Box(ODESystem(ode, True), neighborhood(eps, odevars)))

    Forall(
      eps :: Nil,
      Imply(
        Greater(eps, zero),
        Exists(del :: Nil, And(Greater(del, zero), odevars.foldRight(inner: Formula)((v, f) => Forall(v :: Nil, f)))),
      ),
    )
  }

  /**
   * Attractivity
   * @param ode
   *   the ODE
   * @return
   *   Formula specifying attractivity of the origin for the input ODE
   */
  def attrODE(ode: DifferentialProgram): Formula = {
    val eps = TacticHelper.freshNamedSymbol(Variable("eps"), Box(ode, True))
    val del = TacticHelper.freshNamedSymbol(Variable("del"), Box(ode, True))
    val zero = Number(0)

    val odevars = DifferentialProduct
      .listify(ode)
      .map {
        case AtomicODE(xp, _) => xp.x
        case _ => throw new IllegalArgumentException("attractivity only for concrete ODEs")
      }

    val inner = Imply(
      neighborhood(del, odevars),
      Forall(
        eps :: Nil,
        Imply(Greater(eps, zero), Diamond(ODESystem(ode, True), Box(ODESystem(ode, True), neighborhood(eps, odevars)))),
      ),
    )

    Exists(del :: Nil, And(Greater(del, zero), odevars.foldRight(inner: Formula)((v, f) => Forall(v :: Nil, f))))
  }

  /**
   * Exponential stability
   * @param ode
   *   the ODE
   * @param P
   *   the region of exponential stability
   * @return
   *   Formula specifying exponential stability of the origin for the input ODE with respect to formula P
   */
  def estabODEP(ode: DifferentialProgram, P: Formula): Formula = {
    val alpha = TacticHelper.freshNamedSymbol(Variable("alp"), Box(ode, P))
    val beta = TacticHelper.freshNamedSymbol(Variable("beta"), Box(ode, P))
    val aux = TacticHelper.freshNamedSymbol(Variable("aux"), Box(ode, P))
    val zero = Number(0)

    val odevars = DifferentialProduct
      .listify(ode)
      .map {
        case AtomicODE(xp, _) => xp.x
        case _ => throw new IllegalArgumentException("attractivity only for concrete ODEs")
      }

    val norm = dot_prod(odevars, odevars)

    val odeext = DifferentialProduct(AtomicODE(DifferentialSymbol(aux), Times(Number(-2), Times(beta, aux))), ode)

    val inner = Imply(
      P,
      Box(Compose(Assign(aux, Times(Times(alpha, alpha), norm)), ODESystem(odeext, True)), LessEqual(norm, aux)),
    )

    Exists(
      alpha :: Nil,
      And(
        Greater(alpha, zero),
        Exists(beta :: Nil, And(Greater(beta, zero), odevars.foldRight(inner: Formula)((v, f) => Forall(v :: Nil, f)))),
      ),
    )
  }
}
