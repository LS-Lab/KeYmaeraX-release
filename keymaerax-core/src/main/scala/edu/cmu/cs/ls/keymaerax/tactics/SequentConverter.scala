/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction, TraverseToPosition}
import edu.cmu.cs.ls.keymaerax.core._

/**
 * Additional implicit functions defined for sequents when imported.
 * @author Andre Platzer
 */
object SequentConverter {
  import scala.language.implicitConversions
  implicit def SequentToSequentConverter(s: Sequent): SequentConverter = new SequentConverter(s)
}
class SequentConverter(val seq: Sequent) {
  def apply(pos: Position): Expression = new FormulaConverter(seq(pos.top)).apply(pos.inExpr)
  /** Subexpression at indicated position */
  def at(pos: Position): Option[Expression] = try { new FormulaConverter(seq(pos.top)).at(pos.inExpr) } catch {
    case e: NoSuchElementException   => println("ill-positioned " + pos + " in " + seq + " since " + e); None
    case e: IllegalArgumentException => println("ill-positioned " + pos + " in " + seq + " since " + e); None
  }

  /**
   * Split formula at a position into sub-expression at that position and the context in which it occurs.
   * @param pos The position pointing to the expression.
   * @return A tuple (p(.), e) of context p(.) and sub-expression e, where p(e) is equivalent to fml.
   */
  def splitContext(pos: Position): (Context[Formula], Expression) = new FormulaConverter(seq(pos.top)).extractContext(pos.inExpr)

  /** Returns the subformula of fml at position pos */
  def subFormulaAt(pos: Position): Option[Formula] = new FormulaConverter(seq(pos.top)).subFormulaAt(pos.inExpr)

  /** Returns the term at position pos in fml. */
  def termAt(pos: Position): Term = new FormulaConverter(seq(pos.top)).termAt(pos.inExpr)
}
