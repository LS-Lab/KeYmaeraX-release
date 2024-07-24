/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.macros

// TODO Convert into enum after updating to Scala 3
sealed trait Unifier

object Unifier {

  /** General unification. */
  case object Full extends Unifier

  /**
   * No symbol can occur twice in the shape. If a symbol does occur twice, it is assumed that the identical match is
   * found in all use cases, which is a strong assumption and can lead to unpredictable behavior otherwise.
   */
  case object Linear extends Unifier

  /**
   * A formula is surjective iff rule US can instantiate it to any of its axiom schema instances, so those obtained by
   * uniformly replacing program constant symbols by hybrid games and unit predicationals by formulas. If no arguments
   * occur, so no function or predicate symbols or predicationals, then the axiom is surjective. UnitFunctional,
   * UnitPredicational, ProgramConst etc. can still occur. Function or predicate symbols that occur in a context without
   * any bound variables are exempt. For example [[Ax.testb]].
   */
  case object Surjective extends Unifier

  /** Both [[Surjective]] and [[Linear]]. */
  case object SurjectiveLinear extends Unifier

  /** An axiom that pretends to be surjective and linear even if it isn't necessarily so. */
  case object SurjectiveLinearPretend extends Unifier
}
