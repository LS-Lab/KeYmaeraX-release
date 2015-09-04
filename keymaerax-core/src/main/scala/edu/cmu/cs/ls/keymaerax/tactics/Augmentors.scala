/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._

/**
 * If imported, automatically augments core data structures with convenience wrappers for tactic purposes.
 * @author Andre Platzer
 * @see [[Context]]
 */
object Augmentors {

  /**
   * Augment terms with additional tactics-only helper functions.
   * @author Andre Platzer
   */
  implicit class TermAugmentor(val term: Term) {
    /** Subexpression at indicated position */
    def apply(pos: PosInExpr): Expression = at(pos)._2
    /** Split into expression and its context at the indicated position */
    def at(pos: PosInExpr): (Context[Term], Expression) = Context.at(term, pos)
  }

  /**
   * Augment formulas with additional tactics-only helper functions.
   * @author Andre Platzer
   */
  implicit class FormulaAugmentor(val fml: Formula) {
    /** Subexpression at indicated position */
    def apply(pos: PosInExpr): Expression = at(pos)._2
    /** Split into expression and its context at the indicated position */
    def at(pos: PosInExpr): (Context[Formula], Expression) = Context.at(fml, pos)
  }

  /**
   * Augment programs with additional tactics-only helper functions.
   * @author Andre Platzer
   */
  implicit class ProgramAugmentor(val prog: Program) {
    /** Subexpression at indicated position */
    def apply(pos: PosInExpr): Expression = at(pos)._2
    /** Split into expression and its context at the indicated position */
    def at(pos: PosInExpr): (Context[Program], Expression) = Context.at(prog, pos)
  }

  /**
   * Augment sequent with additional tactics-only helper functions.
   * @author Andre Platzer
   */
  implicit class SequentAugmentor(val seq: Sequent) {
    /** Subexpression at indicated position */
    def apply(pos: Position): Expression = FormulaAugmentor(seq(pos.top))(pos.inExpr)
    /** Split into expression and itsla*  *formucontext at the indicated position */
    def at(pos: Position): (Context[Formula], Expression) = FormulaAugmentor(seq(pos.top)).at(pos.inExpr)
  }
}