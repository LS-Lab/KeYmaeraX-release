/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools.ext

import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.lemma.Lemma

/** Goals for parallel QE execution. */
trait Goal
/** A single formula. */
case class Atom(goal: Formula) extends Goal
/** One of the goals must be proved. */
case class OneOf(goals: Seq[Goal]) extends Goal
/** All of the goals must be proved. */
case class AllOf(goals: Seq[Goal]) extends Goal

/**
  * Quantifier elimination tool that combines trusted [[edu.cmu.cs.ls.keymaerax.core.QETool]] with other untrusted tools
  * (so that tools implementing [[QETacticTool]] can forward to a trusted [[edu.cmu.cs.ls.keymaerax.core.QETool]]
  * without being trusted themselves).
  */
trait QETacticTool {
  /**
    * Returns a lemma witnessing equivalence between a quantifier-free formula and the specified formula.
    * @param formula The formula whose quantifier-free equivalent is sought.
    * @return A lemma showing equivalence between `formula` and a quantifier-free formula, with tool evidence.
    */
  def qe(formula: Formula): Lemma

  /** Returns the result of the first-to-finish (sub-)goal in `g` (result of the first-to-finish sub-goal of [[OneOf]],
    * else result of [[Atom]] or [[AllOf]]). */
  def qe(g: Goal): (Goal, Formula)
}
