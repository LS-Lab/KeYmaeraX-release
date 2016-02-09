/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{StopTraversal, ExpressionTraversalFunction}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.{TopPosition, PosInExpr, Position}

/**
 * If imported, automatically augments core data structures with convenience wrappers for tactic purposes
 * such as subexpression positioning, context splitting, and replacements.
  *
 * @example To use this implicit augmentation automatically, import it via
  * {{{
  *   import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
  * }}}
  * Then use it as if its methods were part of the data structures
  * {{{
  *   val parser = KeYmaeraXParser
  *   val f = parser("x^2>=0 & x<44 -> [x:=2;{x'=1&x<=10}]x>=1")
  *   // will obtain the x>=1 part
  *   val someSub = f.sub(PosInExpr(1::1::Nil))
  *   println(someSub)
  *   // construct x^2>=0 & x<44 -> [x:=2;{x'=1&x<=10}]x^2>y
  *   val other = f.replaceAt(PosInExpr(1::1::Nil), parser("x^2>y"))
  *   println(other)
  * }}}
 * @author Andre Platzer
 * @see [[Context]]
 */
object Augmentors {

  /**
    * Augment expressions with additional tactics-only helper functions.
    * @author Andre Platzer
    */
//  implicit class ExpressionAugmentor(val expr: Expression) {
//  }

  /**
   * Augment terms with additional tactics-only helper functions.
   * @author Andre Platzer
   */
  implicit class TermAugmentor(val term: Term) {
    /** Subexpression at indicated position */
    def apply(pos: PosInExpr): Expression = at(pos)._2
    /** Subexpression at indicated position if exists, or None */
    def sub(pos: PosInExpr): Option[Expression] = try {Some(Context.sub(term, pos))} catch {case e: IllegalArgumentException => None}
    /** Split into expression and its context at the indicated position */
    def at(pos: PosInExpr): (Context[Term], Expression) = Context.at(term, pos)
    /** Replace at position pos by repl */
    def replaceAt(pos: PosInExpr, repl: Expression): Expression = Context.replaceAt(term, pos, repl)
    /**
      * Find the first (i.e., left-most) position of a subexpression satisfying `condition`, if any.
      * @param condition the condition that the subexpression sought for has to satisfy.
      * @return The first position, or None if no subexpression satisfies `condition`.
      */
    def find(condition: Term => Boolean): Option[PosInExpr] = {
      var pos: Option[PosInExpr] = None
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
          if (condition(e.asInstanceOf[Term])) { pos = Some(p); Left(Some(ExpressionTraversal.stop)) }
          else Left(None)
      }, term)
      pos
    }
  }

  /**
   * Augment formulas with additional tactics-only helper functions.
   * @author Andre Platzer
   */
  implicit class FormulaAugmentor(val fml: Formula) {
    /** Subexpression at indicated position */
    def apply(pos: PosInExpr): Expression = at(pos)._2
    /** Subexpression at indicated position if exists, or None*/
    def sub(pos: PosInExpr): Option[Expression] = try {Some(Context.sub(fml, pos))} catch {case e: IllegalArgumentException => None}
    /** Split into expression and its context at the indicated position */
    def at(pos: PosInExpr): (Context[Formula], Expression) = Context.at(fml, pos)
    /** Replace at position pos by repl */
    def replaceAt(pos: PosInExpr, repl: Expression): Expression = Context.replaceAt(fml, pos, repl)
    /**
      * Find the first (i.e., left-most) position of a subexpression satisfying `condition`, if any.
      * @param condition the condition that the subexpression sought for has to satisfy.
      * @return The first position and the subexpression at that position, or None if no subexpression satisfies `condition`.
      */
    def find(condition: Expression => Boolean): Option[(PosInExpr,Expression)] = {
      var pos: Option[(PosInExpr,Expression)] = None
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] =
          if (condition(e)) { pos = Some((p,e)); Left(Some(ExpressionTraversal.stop)) }
          else Left(None)
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] =
          if (condition(e)) { pos = Some((p,e)); Left(Some(ExpressionTraversal.stop)) }
          else Left(None)
      }, fml)
      pos
    }
    /**
      * Find the first (i.e., left-most) position of a subformula satisfying `condition`, if any.
      * @param condition the condition that the subformula sought for has to satisfy.
      * @return The first position and subformula at that position, or None if no subformula satisfies `condition`.
      */
    def findSubformula(condition: Formula => Boolean): Option[(PosInExpr,Formula)] = {
      var pos: Option[(PosInExpr,Formula)] = None
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] =
          if (condition(e)) { pos = Some((p,e)); Left(Some(ExpressionTraversal.stop)) }
          else Left(None)
      }, fml)
      pos
    }

    /** Returns true if the formula is FOL, false otherwise. */
    def isFOL: Boolean = {
      var result = true
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
          case Box(_, _) => result = false; Left(Some(ExpressionTraversal.stop))
          case Diamond(_, _) => result = false; Left(Some(ExpressionTraversal.stop))
          case _ => Left(None)
        }
      }, fml)
      result
    }
  }

  /**
   * Augment programs with additional tactics-only helper functions.
   * @author Andre Platzer
   */
  implicit class ProgramAugmentor(val prog: Program) {
    /** Subexpression at indicated position */
    def apply(pos: PosInExpr): Expression = at(pos)._2
    /** Subexpression at indicated position if exists, or None*/
    def sub(pos: PosInExpr): Option[Expression] = try {Some(Context.sub(prog,pos))} catch {case e: IllegalArgumentException => None}
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
    /** Subexpression at indicated position if exists, or None */
    def sub(pos: Position): Option[Expression] = if (pos.isIndexDefined(seq)) FormulaAugmentor(seq(pos.top)).sub(pos.inExpr) else None
    /** Split into expression and its *formula* context at the indicated position */
    def at(pos: Position): (Context[Formula], Expression) = FormulaAugmentor(seq(pos.top)).at(pos.inExpr)
    /** Replace at position pos by repl */
    def replaceAt(pos: Position, repl: Expression): Expression = FormulaAugmentor(seq(pos.top)).replaceAt(pos.inExpr, repl)
    //@todo implement returning both Ante+Succ
    def zipWithPositions: List[(Formula, TopPosition)] = ???
    /** Convert a sequent to its equivalent formula `/\antes -> \/succs` */
    def toFormula: Formula = {
      val anteAnd = seq.ante.reduceRightOption(And).getOrElse(True)
      val succOr = seq.succ.reduceRightOption(Or).getOrElse(False)
      //@note don't optimize true-> and ->false, since otherwise we'll have to deal with two special cases
      Imply(anteAnd, succOr)
    }
  }
}
