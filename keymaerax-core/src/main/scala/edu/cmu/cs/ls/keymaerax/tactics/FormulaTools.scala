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
   * Returns the polarity of the subformula at position pos in formula.
   * @param formula The formula.
   * @param pos The position within formula for which the polarity is searched.
   * @return -1 for negative polarity, 1 for positive polarity, 0 for unknown polarity.
   */
  def polarityAt(formula: Formula, pos: PosInExpr): Int =
    if (pos.pos.isEmpty) 1 else formula match {
      case Not(g) => require(pos.head == 0, "Unary operator must have position head 0, but was " + pos); -polarityAt(g, pos.child)
      case Imply(l, _) if pos.head == 0 => -polarityAt(l, pos.child)
      case Imply(_, r) if pos.head == 1 => polarityAt(r, pos.child)
      case Equiv(_, _) => 0
      case f: UnaryCompositeFormula  => require(pos.head == 0, "Unary operator must have position head 0, but was " + pos); polarityAt(f.child, pos.child)
      case f: BinaryCompositeFormula if pos.head == 0 => polarityAt(f.left, pos.child)
      case f: BinaryCompositeFormula if pos.head == 1 => polarityAt(f.right, pos.child)
      case f: Modal                  => require(pos.head == 1, "Modal operator must have position head 1, but was " + pos); polarityAt(f.child, pos.child)
      case f: Quantified             => require(pos.head == 1, "Quantified must have position head 1, but was " + pos); polarityAt(f.child, pos.child)
    }

  /**
   * Returns a formula with equivalences turned into implications such that the polarity of the subformula at position
   * pos has the specified polarity.
   * Creates a variation of this formula which has equivalences reoriented such that the polarity
   * of the subformula at position pos in the resulting formula will be the desired polarity.
   * @param formula The formula.
   * @param pos The position within formula for which the polarity is supposed to be changed to the desired polarity.
   * @param polarity The desired polarity, must be either 1 (positive polarity) or -1 (negative polarity).
   * @return The formula with equivalences turned into implications.
   */
  def makePolarityAt(formula: Formula, pos: PosInExpr, polarity: Int): Formula = {
    require(polarity == 1 || polarity == -1, "Polarity must be either positive or negative")
    if (pos.pos.isEmpty && polarity == 1) formula
    else if (pos.pos.isEmpty && polarity == -1) Not(formula)
    else formula match {
      case Equiv(l, r) if pos.head == 0 && polarityAt(l, pos.child) * polarity == -1 => Imply(l, r)
      case Equiv(l, r) if pos.head == 0 && polarityAt(l, pos.child) * polarity ==  1 => Imply(r, l)
      case Equiv(l, r) if pos.head == 0 && polarityAt(l, pos.child) * polarity ==  0 => Imply(makePolarityAt(l, pos.child, -polarity), r)
      case Equiv(l, r) if pos.head == 1 && polarityAt(r, pos.child) * polarity == -1 => Imply(r, l)
      case Equiv(l, r) if pos.head == 1 && polarityAt(r, pos.child) * polarity ==  1 => Imply(l, r)
      case Equiv(l, r) if pos.head == 1 && polarityAt(r, pos.child) * polarity ==  0 => Imply(l, makePolarityAt(r, pos.child, polarity))
      case f: UnaryCompositeFormula  => require(pos.head == 0, "Unary operator must have position head 0, but was " + pos); f.reapply(makePolarityAt(f.child, pos.child, polarity))
      case f: BinaryCompositeFormula if pos.head == 0 => f.reapply(makePolarityAt(f.left, pos.child, polarity), f.right)
      case f: BinaryCompositeFormula if pos.head == 1 => f.reapply(f.left, makePolarityAt(f.right, pos.child, polarity))
      case f: Modal                  => require(pos.head == 1, "Modal operator must have position head 1, but was " + pos); f.reapply(f.program, makePolarityAt(f.child, pos.child, polarity))
      case f: Quantified             => require(pos.head == 1, "Quantified must have position head 1, but was " + pos); f.reapply(f.vars, makePolarityAt(f.child, pos.child, polarity))
    }
  }

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
