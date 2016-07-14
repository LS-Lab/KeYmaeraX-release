/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics._
import edu.cmu.cs.ls.keymaerax.btactics.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.btactics.{ExpressionTraversal, ProofRuleTactics}
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.signanalysis.SignAnalysis
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tools.CounterExampleTool

import scala.collection.mutable.ListBuffer
import scala.language.postfixOps

/**
  * Tactics for simplifying arithmetic sub-goals.
  * @author Stefan Mitsch
  */
object ArithmeticSpeculativeSimplification {

  /** Tries decreasingly aggressive strategies of hiding formulas before QE, until finally falling back to full QE if none
    * of the simplifications work out. */
  def speculativeQE(implicit tool: QETool with CounterExampleTool): BelleExpr = "QE" by ((sequent: Sequent) => {
    (print("Trying abs...") & proveOrRefuteAbs & print("...abs done")) | speculativeQENoAbs
  })

  /** QE without handling abs */
  private def speculativeQENoAbs(implicit tool: QETool with CounterExampleTool): BelleExpr = "QE" by ((sequent: Sequent) => {
    (print("Trying orIntro and smart hiding...") & (orIntro((print("Bound") & hideNonmatchingBounds & smartHide & QE()) | (print("Non-Bound") & smartHide & QE())) & print("... orIntro and smart hiding successful"))) |
    (print("orIntro failed, trying smart hiding...") & ((hideNonmatchingBounds & smartHide & QE()) | (smartHide & QE())) & print("...smart hiding successful")) |
    (print("All simplifications failed, falling back to ordinary QE") & QE())
  })

  /** Uses the disjunction introduction proof rule to prove a disjunctions by proving any 1 of the disjuncts. */
  def orIntro(finish: BelleExpr): BelleExpr = "orIntro" by ((sequent: Sequent) => {
    def toSingleSucc(retain: Int): BelleExpr = {
      sequent.succ.indices.filter(_ != retain).sorted.reverse.map(i => hideR(i+1)).reduceLeft[BelleExpr](_&_)
    }

    if (sequent.succ.size > 1) {
      //@todo CounterExample might provide insight on which of the formulas are needed
      sequent.succ.indices.map(i => toSingleSucc(i) & finish).reduceLeft[BelleExpr](_|_) | finish
    } else finish
  })

  /** Proves abs by trying to find contradictions; falls back to QE if contradictions fail */
  def proveOrRefuteAbs(implicit tool: QETool with CounterExampleTool): BelleExpr = "proveOrRefuteAbs" by ((sequent: Sequent) => {
    val symbols = (sequent.ante.flatMap(StaticSemantics.symbols) ++ sequent.succ.flatMap(StaticSemantics.symbols)).toSet
    if (symbols.exists(_.name == "abs")) exhaustiveAbsSplit & OnAll((hideR('R)*@TheType() & assertNoCex & QE()) | speculativeQENoAbs)
    else error("Sequent does not contain abs")
  })

  /** Splits absolute value functions to create more, but hopefully simpler, goals. */
  def exhaustiveAbsSplit: BelleExpr = "absSplit" by ((sequent: Sequent) => {
    def absPos(fml: Formula): List[PosInExpr] = {
      val result = ListBuffer[PosInExpr]()
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
          case FuncOf(Function("abs", _, _, _, true), _) => result += p; Left(None)
          case _ => Left(None)
        }
      }, fml)
      result.toList
    }

    val anteAbs = sequent.ante.zipWithIndex.
      filter{ case (f,i) => StaticSemantics.symbols(f).contains(Function("abs", None, Real, Real))}.
      map{ case (f, i) => (f, AntePosition.base0(i)) }
    val succAbs = sequent.succ.zipWithIndex.
      filter{ case (f,i) => StaticSemantics.symbols(f).contains(Function("abs", None, Real, Real))}.
      map{ case (f,i) => (f, SuccPosition.base0(i)) }

    val absTactic = (anteAbs++succAbs).
      //@note p+inExpr navigates to sub-expression since p are top
      map{ case (f,p) => (f, absPos(f).map(inExpr => p + inExpr)) }.
      map{ case (f,p) => p.map(pos => OnAll(abs(pos) & orL('Llast) partial)).reduceLeft[BelleExpr](_&_) }.
      reduceLeft[BelleExpr](_&_)

    absTactic & OnAll(andL('_)*@TheType() partial) & OnAll(exhaustiveEqL2R(hide=true)('L)*@TheType() partial)
  })

  /** Assert that there is no counter example. skip if none, error if there is. */
  def assertNoCex(implicit tool: CounterExampleTool): BelleExpr = "assertNoCEX" by ((sequent: Sequent) => {
    tool.findCounterExample(sequent.toFormula) match {
      case Some(cex) => error("Found counterexample " + cex)
      case None => skip
    }
  })

  /** Hides formulas with non-matching bounds. */
  def hideNonmatchingBounds: BelleExpr = "hideNonmatchingBounds" by ((sequent: Sequent) => {
    SignAnalysis.boundHideCandidates(sequent).sortBy(_.getIndex).reverse.map(hide(_)).reduceLeftOption[BelleExpr](_&_).getOrElse(skip)
  })

  def hideInconsistentSigns: BelleExpr = "hideInconsistentBounds" by ((sequent: Sequent) => {
    SignAnalysis.signHideCandidates(sequent).sortBy(_.getIndex).reverse.map(hide(_)).reduceLeftOption[BelleExpr](_&_).getOrElse(skip)
  })

}