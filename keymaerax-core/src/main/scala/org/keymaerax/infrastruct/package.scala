/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax

import org.keymaerax.core.Expression

import scala.collection.immutable

/**
 * The infrastruct package provides central prover infrastructure such as unification and augmented formula analysis.
 * This infrastructure is of basic interest and useful independently of any particular tactic language etc.
 *
 * Main functionality:
 *   - [[Position Position]] with [[PosInExpr]] positioning within subformulas.
 *   - [[Context Context]] Convenience representation of formulas used as contexts that provide ways of substituting
 *     expressions in by conceptually splitting and managing the context around a position in a formula.
 *   - [[RenUSubst RenUSubst]] Renaming Uniform Substitutions that quickly combine and ultimately reduce to uniform
 *     renaming and uniform substitution of the kernel.
 *   - [[UnificationMatch UnificationMatch]] single-sided matching unification algorithms.
 *   - [[Augmentors Augmentors]]: Implicit convenience additions of helper functions to formulas, terms, programs,
 *     sequents that are useful for analysis and transformation.
 *   - [[ExpressionTraversal ExpressionTraversal]] generic functionality for traversing expressions for analysis or
 *     transformation.
 *
 * @author
 *   Andre Platzer
 * @see
 *   [[org.keymaerax.btactics.UnifyUSCalculus]]
 */
package object infrastruct {

  /** Choice of standalone Renaming Uniform Substitution operation implementation */
  type USubstRen = USubstRenOne

  /**
   * USubstRen factory method for standalone Renaming Uniform Substitution operation implementation, forwards to
   * constructor.
   */
  def USubstRen(subsDefsInput: immutable.Seq[(Expression, Expression)]): USubstRen = USubstRenOne(subsDefsInput)
}
