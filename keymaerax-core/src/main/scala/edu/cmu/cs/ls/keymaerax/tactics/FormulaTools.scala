/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.Augmentors.FormulaAugmentor

/**
 * Tactic tools for formula manipulation and extraction.
 * @author Andre Platzer
 */
object FormulaTools {
  // formula tools

  /**
   * Split a formula into its conjuncts.
   * Without performing clause form or CNF or DNF transformations.
   * @example conjuncts(p() & q() & (r() & (s() | t()&u()))) == List(p(), q(), r(), s()|t()&u())
   */
  def conjuncts(formula: Formula): List[Formula] = formula match {
    case And(p,q) => conjuncts(p) ++ conjuncts(q)
    case f => List(f)
  }

  /**
   * Split a formula into its disjuncts.
   * Without performing clause form or CNF or DNF transformations.
   * @example disjuncts(p() | q() | (r() | (s() & (t()|u())))) == List(p(), q(), r(), s()&(t()|u()))
   */
  def disjuncts(formula: Formula): List[Formula] = formula match {
    case Or(p,q) => disjuncts(p) ++ disjuncts(q)
    case f => List(f)
  }

  /**
   * Computes the polarity of the subformula at position pos in formula.
   * @param formula The formula.
   * @param pos The position within formula for which the polarity is searched.
   * @return -1 for negative polarity, 1 for positive polarity, 0 for unknown polarity.
   */
  def polarityAt(formula: Formula, pos: PosInExpr): Int =
    if (pos.pos.isEmpty) 1 else FormulaAugmentor(formula).at(pos.parent) match {
      case (_, Not(_)) => -polarityAt(formula, pos.parent)
      case (_, Imply(_, _)) if pos.pos.last == 0 => -polarityAt(formula, pos.parent)
      case (_, Imply(_, _)) if pos.pos.last == 1 => polarityAt(formula, pos.parent)
      case (_, Equiv(_, _)) => 0
      case _ => polarityAt(formula, pos.parent)
    }

}
