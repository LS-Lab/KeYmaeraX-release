/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.utils

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, PosInExpr, TacticStatistics}
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{ExpressionTraversalFunction, FTPG, StopTraversal}
import edu.cmu.cs.ls.keymaerax.core._

/** Formula, term, and tactic statistics.
  * @author Stefan Mitsch
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
  private def doCountAtomicTerms[T: FTPG](e: T): Int = {
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
}
