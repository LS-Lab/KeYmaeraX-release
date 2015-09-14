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
    /** Subexpression at indicated position if exists, or None */
    def sub(pos: PosInExpr): Option[Expression] = try {Some(at(pos)._2)} catch {case e: IllegalArgumentException => None}
    /** Split into expression and its context at the indicated position */
    def at(pos: PosInExpr): (Context[Term], Expression) = Context.at(term, pos)
    /** Replace at position pos by repl */
    def replaceAt(pos: PosInExpr, repl: Expression): Expression = Context.replaceAt(term, pos, repl)
  }

  /**
   * Augment formulas with additional tactics-only helper functions.
   * @author Andre Platzer
   */
  implicit class FormulaAugmentor(val fml: Formula) {
    /** Subexpression at indicated position */
    def apply(pos: PosInExpr): Expression = at(pos)._2
    /** Subexpression at indicated position if exists, or None*/
    def sub(pos: PosInExpr): Option[Expression] = try {Some(at(pos)._2)} catch {case e: IllegalArgumentException => None}
    /** Split into expression and its context at the indicated position */
    def at(pos: PosInExpr): (Context[Formula], Expression) = Context.at(fml, pos)
    /** Replace at position pos by repl */
    def replaceAt(pos: PosInExpr, repl: Expression): Expression = Context.replaceAt(fml, pos, repl)
  }

  /**
   * Augment programs with additional tactics-only helper functions.
   * @author Andre Platzer
   */
  implicit class ProgramAugmentor(val prog: Program) {
    /** Subexpression at indicated position */
    def apply(pos: PosInExpr): Expression = at(pos)._2
    /** Subexpression at indicated position if exists, or None*/
    def sub(pos: PosInExpr): Option[Expression] = try {Some(at(pos)._2)} catch {case e: IllegalArgumentException => None}
    /** Split into expression and its context at the indicated position */
    def at(pos: PosInExpr): (Context[Program], Expression) = Context.at(prog, pos)
    /** Replace at position pos by repl */
    def replaceAt(pos: PosInExpr, repl: Expression): Expression = Context.replaceAt(prog, pos, repl)
  }

  /**
   * Augment sequent with additional tactics-only helper functions.
   * @author Andre Platzer
   */
  implicit class SequentAugmentor(val seq: Sequent) {
    /** Subexpression at indicated position */
    def apply(pos: Position): Expression = FormulaAugmentor(seq(pos.top))(pos.inExpr)
    /** Subexpression at indicated position if exists, or None*/
    def sub(pos: Position): Option[Expression] = FormulaAugmentor(seq(pos.top)).sub(pos.inExpr)
    /** Split into expression and its *formula* context at the indicated position */
    def at(pos: Position): (Context[Formula], Expression) = FormulaAugmentor(seq(pos.top)).at(pos.inExpr)
    /** Replace at position pos by repl */
    def replaceAt(pos: Position, repl: Expression): Expression = FormulaAugmentor(seq(pos.top)).replaceAt(pos.inExpr, repl)
  }
}