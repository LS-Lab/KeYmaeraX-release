/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, TacticStatistics}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}

/** Formula, term, and tactic statistics.
  * @author Stefan Mitsch
  * @author Andre Platzer
  */
object Statistics {

  /** Returns the number of composition operators in the formula `fml`
    * @param arith true to include counting arithmetic operators. */
  def countFormulaOperators(fml: Formula, arith: Boolean = false): Int = {
    var numOperators = 0
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
        case _: CompositeFormula => numOperators += 1; Left(None)
        case _ => Left(None)
      }

      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case _: CompositeTerm => if (arith) numOperators += 1; Left(None)
        case _ => Left(None)
      }

      override def preP(p: PosInExpr, e: Program): Either[Option[StopTraversal], Program] = e match {
        case _: CompositeProgram => numOperators += 1; Left(None)
        case _ => Left(None)
      }
    }, fml)
    numOperators
  }

  /** The number of atomic formulas in formula `fml`. */
  def countAtomicFormulas(fml: Formula): Int = {
    var numAtoms = 0
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preF(p: PosInExpr, e: Formula): Either[Option[StopTraversal], Formula] = e match {
        case _: AtomicFormula => numAtoms += 1; Left(None)
        case _ => Left(None)
      }
    }, fml)
    numAtoms
  }

  /** The number of atomic terms in formula `fml`. */
  def countAtomicTerms(fml: Formula): Int = doCountAtomicTerms(fml)

  /** The number of atomic terms in term `trm` */
  def countAtomicTerms(trm: Term): Int = doCountAtomicTerms(trm)

  /** The number of atomic terms in expression `e`. */
  private def doCountAtomicTerms[T <: Expression](e: T): Int = {
    var numAtoms = 0
    ExpressionTraversal.traverse(new ExpressionTraversalFunction {
      override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
        case _: AtomicTerm => numAtoms += 1; Left(None)
        case _ => Left(None)
      }
    }, e)
    numAtoms
  }

  /** The number of tactic operators. See [[TacticStatistics.size]] */
  def tacticSize(t: BelleExpr): Int = TacticStatistics.size(t)
  /** The number of tactic lines. See [[TacticStatistics.lines]] */
  def tacticLines(t: BelleExpr): Int = TacticStatistics.lines(t)


  /** Length of term e, i.e., number of operators and atoms */
  def length(e: Term): Int = e match {
    case e: UnaryCompositeTerm  => 1 + length(e.child)
    case e: BinaryCompositeTerm => 1 + length(e.left) + length(e.right)
    case e: FuncOf              => 1 + length(e.child)
    case _: AtomicTerm          => 1
  }

  /** Length of formula e, i.e., number of operators and atoms */
  def length(e: Formula): Int = e match {
    case e: UnaryCompositeFormula  => 1 + length(e.child)
    case e: BinaryCompositeFormula => 1 + length(e.left) + length(e.right)
    case e: ComparisonFormula      => 1 + length(e.left) + length(e.right)
    case e: PredOf                 => 1 + length(e.child)
    case e: PredicationalOf        => 1 + length(e.child)
    case e: Quantified             => 1 + length(e.child)
    case e: Modal                  => 1 + length(e.program) + length(e.child)
    case _: AtomicFormula          => 1
  }

  /** Length of program e, i.e., number of operators and atoms */
  def length(e: Program): Int = e match {
    case e: UnaryCompositeProgram  => 1 + length(e.child)
    case e: BinaryCompositeProgram => 1 + length(e.left) + length(e.right)
    case e: Assign                 => 1 + length(e.e)
    case e: Test                   => 1 + length(e.cond)
    // don't double-count ODESystem so don't add 1
    case e: ODESystem              => length(e.ode) + length(e.constraint)
    case e: AtomicODE              => 1 + length(e.e)
    case e: DifferentialProduct    => 1 + length(e.left) + length(e.right)
    case _: AtomicProgram          => 1
  }
}
