/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable._

/**
 * LinearMatcher(shape, input) matches second argument `input` against the LINEAR pattern `shape` of the first argument
 * but not vice versa. Matcher leaves input alone and only substitutes into linear shape.
 *
 * Linear matchers require linear shapes, so no symbol can occur twice in the shape. If a symbol does occur twice, it is
 * assumed that the identical match is found in all use cases, which is a strong assumption and can lead to
 * unpredictable behavior. Implemented by a fast single pass. Possibly depends on using straight [[USubstRenOne]]
 *
 * @example
 *   Matching the formula on the right against a linear pattern shape
 *   {{{
 *   LinearMatcher.unify("[a;](p(||)&q(||))".asFormula, "[x:=2*x;{x'=5}](0<=x&x>=y)".asFormula)
 *   }}}
 * @example
 *   Except when lucky, nonlinear patterns will not be matched correctly by LinearMatcher even if they are unifiable.
 *   {{{
 *   LinearMatcher.unify("p(f())<->[x:=f()]p(x)".asFormula, "(2*x)^2>=2*x<->[x:=2*x;]x^2>=x".asFormula)
 *   }}}
 * @author
 *   Andre Platzer
 */
object LinearMatcher extends SchematicUnificationMatch {
  override protected def unifier(e1: Expression, e2: Expression, us: List[SubstRepl]): Subst = {
    val s = Subst(us.distinct)
    logger.debug("  unify: " + e1.prettyString + "\n  with:  " + e2.prettyString + "\n  via:   " + s)
    s
  }

  override protected def unifier(e1: Sequent, e2: Sequent, us: List[SubstRepl]): Subst = {
    val s = Subst(us.distinct)
    logger.debug("  unify: " + e1.prettyString + "\n  with:  " + e2.prettyString + "\n  via:   " + s)
    s
  }

  /**
   * Composition of renaming substitution representations: compose(after, before) gives the representation of `after`
   * performed after `before`.
   */
  override protected def compose(
      after: List[(Expression, Expression)],
      before: List[(Expression, Expression)],
  ): List[(Expression, Expression)] = before ++ after

  /**
   * unifies(s1,s2, t1,t2) unifies (s1,s2) against (t1,t2) by matching.
   *
   * Note: because this is for matching purposes, the unifier u1 is not applied to t2 on the right premise.
   */
  override protected def unifies2(
      s1: Expression,
      s2: Expression,
      t1: Expression,
      t2: Expression,
  ): List[(Expression, Expression)] = compose(unify(s1, t1), unify(s2, t2))

  override protected def unifies2(s1: Term, s2: Term, t1: Term, t2: Term): List[(Expression, Expression)] =
    compose(unify(s1, t1), unify(s2, t2))

  override protected def unifies2(s1: Formula, s2: Formula, t1: Formula, t2: Formula): List[(Expression, Expression)] =
    compose(unify(s1, t1), unify(s2, t2))

  override protected def unifies2(s1: Program, s2: Program, t1: Program, t2: Program): List[(Expression, Expression)] =
    compose(unify(s1, t1), unify(s2, t2))

  override protected def unifiesODE2(
      s1: DifferentialProgram,
      s2: DifferentialProgram,
      t1: DifferentialProgram,
      t2: DifferentialProgram,
  ): List[(Expression, Expression)] = compose(unifyODE(s1, t1), unifyODE(s2, t2))

  override protected def unify(s1: Sequent, s2: Sequent): List[SubstRepl] =
    if (!(s1.ante.length == s2.ante.length && s1.succ.length == s2.succ.length)) ununifiable(s1, s2)
    else {
      val combine = (us: List[SubstRepl], st: (Formula, Formula)) => compose(us, unify(st._1, st._2))
      compose(s1.ante.zip(s2.ante).foldLeft(id)(combine), s1.succ.zip(s2.succ).foldLeft(id)(combine))
    }
}
