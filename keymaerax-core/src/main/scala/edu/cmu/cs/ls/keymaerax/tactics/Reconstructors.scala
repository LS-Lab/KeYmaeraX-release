/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import scala.annotation.switch
import scala.collection.immutable._

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Reconstructors for expression data structures that provides them with a copy or clone or reconstruct-same-type function.
 * Generic access to the respective type's apply function.
 * Created by aplatzer on 9/13/15.
 * @author Andre Platzer
 */
object Reconstructors {
  //  def reconstructor[T<:Expression](e: T with BinaryComposite): (T,T)=>T = e match {
  //    case _: Plus   => Plus.apply
  //    case _: Minus  => Minus.apply
  //  }

  /** Reconstructor for unary term of type e */
  @inline
  def reconstruct(e: UnaryCompositeTerm): Term=>Term = {(e : @switch) match {
    case _: Neg => Neg.apply
    case _: Differential => Differential.apply
  }
  } //ensuring(r => r(Number(5),Number(5)).getClass==e.getClass, "Reconstructor reconstructs of same type as e " + e)

  /** Reconstructor for binary term of type e */
  @inline
  def reconstruct(e: BinaryCompositeTerm): (Term,Term)=>Term = {(e : @switch) match {
    case _: Plus   => Plus.apply
    case _: Minus  => Minus.apply
    case _: Times  => Times.apply
    case _: Divide => Divide.apply
    case _: Power  => Power.apply
    case _: Pair   => Pair.apply
  }
  } //ensuring(r => r(Number(5),Number(5)).getClass==e.getClass, "Reconstructor reconstructs of same type as e " + e)

  /** Reconstructor for unary formula of type e */
  @inline
  def reconstruct(e: UnaryCompositeFormula): Formula=>Formula = {(e : @switch) match {
    case _: Not => Not.apply
    case _: DifferentialFormula => DifferentialFormula.apply
  }
  }

  /** Reconstructor for binary formulas of type e */
  @inline
  def reconstruct(e: BinaryCompositeFormula): (Formula,Formula)=>Formula = {(e : @switch) match {
    case _: And   => And.apply
    case _: Or    => Or.apply
    case _: Imply => Imply.apply
    case _: Equiv => Equiv.apply
  }
  }

  /** Reconstructor for comparison formulas of type e */
  @inline
  def reconstruct(e: ComparisonFormula): (Term,Term)=>Formula = {(e : @switch) match {
    case _: Equal        => Equal.apply
    case _: NotEqual     => NotEqual.apply
    case _: Greater      => Greater.apply
    case _: GreaterEqual => GreaterEqual.apply
    case _: Less      => Less.apply
    case _: LessEqual => LessEqual.apply
  }
  }

  /** Reconstructor for quantified formulas of type e */
  @inline
  def reconstruct(e: Quantified): (Seq[Variable],Formula)=>Formula = {(e : @switch) match {
    case _: Forall => Forall.apply
    case _: Exists => Exists.apply
  }
  }

  /** Reconstructor for modal formulas of type e */
  @inline
  def reconstruct(e: Modal): (Program,Formula)=>Formula = {(e : @switch) match {
    case _: Box     => Box.apply
    case _: Diamond => Diamond.apply
  }
  }

  /** Reconstructor for unary programs of type e */
  @inline
  def reconstruct(e: UnaryCompositeProgram): Program=>Program = {(e : @switch) match {
    case _: Loop => Loop.apply
    case _: Dual  => Dual.apply
  }
  }

  /** Reconstructor for binary programs of type e */
  @inline
  def reconstruct(e: BinaryCompositeProgram): (Program,Program)=>Program = {(e : @switch) match {
    case _: Compose => Compose.apply
    case _: Choice  => Choice.apply
  }
  }

}
