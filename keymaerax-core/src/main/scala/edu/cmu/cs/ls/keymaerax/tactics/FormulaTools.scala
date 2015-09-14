/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.Augmentors.FormulaAugmentor
import edu.cmu.cs.ls.keymaerax.tactics.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}

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
   * @todo optimize implementation, which can be made significantly faster by a direct recursion.
   */
  def polarityAt(formula: Formula, pos: PosInExpr): Int =
    if (pos.pos.isEmpty) 1 else FormulaAugmentor(formula).at(pos.parent) match {
      case (_, Not(_)) => -polarityAt(formula, pos.parent)
      case (_, Imply(_, _)) if pos.pos.last == 0 => -polarityAt(formula, pos.parent)
      case (_, Imply(_, _)) if pos.pos.last == 1 => polarityAt(formula, pos.parent)
      case (_, Equiv(_, _)) => 0
      case _ => polarityAt(formula, pos.parent)
    }

  /**
   * Creates a variation of this formula which has equivalences reoriented such that the polarity
   * of the subformula at position pos in the resulting formula will be the desired polarity.
   * @param formula The formula.
   * @param pos The position within formula for which the polarity is searched.
   * @return -1 for negative polarity, 1 for positive polarity, 0 for unknown polarity.
   * @todo optimize implementation, which can be made significantly faster by a direct recursion.
   */



  /**
   * Returns the first (i.e., left-most) position of subFormula within formula, if any.
   * @param formula The formula to search for containment of subformula.
   * @param subFormula The subformula.
   * @return The first position, or None if subformula is not contained in formula.
   */
  def posOf(formula: Formula, subFormula: Formula): Option[PosInExpr] = {
    var pos: Option[PosInExpr] = None
    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] =
        if (e == subFormula) { pos = Some(p); Left(Some(ExpressionTraversal.stop)) }
        else Left(None)
    }, formula)
    pos
  }

}
