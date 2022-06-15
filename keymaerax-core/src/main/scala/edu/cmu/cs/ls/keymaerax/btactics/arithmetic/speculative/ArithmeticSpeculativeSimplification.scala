/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.arithmetic.speculative

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.ArithmeticSimplification._
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.{ExpressionTraversalFunction, StopTraversal}
import edu.cmu.cs.ls.keymaerax.btactics.{DebuggingTactics, Idioms, ToolTactics}
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.arithmetic.signanalysis.{Sign, SignAnalysis}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, ExpressionTraversal, PosInExpr, SuccPosition}
import edu.cmu.cs.ls.keymaerax.btactics.macros.Tactic
import edu.cmu.cs.ls.keymaerax.parser.InterpretedSymbols

import scala.collection.mutable.ListBuffer

/**
  * Tactics for simplifying arithmetic sub-goals.
  * @author Stefan Mitsch
  */
object ArithmeticSpeculativeSimplification {

  private val DEBUG = true

  /** Tries decreasingly aggressive strategies of hiding formulas before QE, until finally falling back to full QE if none
    * of the simplifications work out. */
  @Tactic(names="Speculative QE",
    codeName="smartQE",
    premises="*",
    //    smartQE -----------
    conclusion="Γ<sub>FOLR</sub> |- Δ<sub>FOLR</sub>",
    displayLevel="browse")
  lazy val speculativeQE: BelleExpr = anon ((_: Sequent) => {
    (DebuggingTactics.debug("Trying abs...", DEBUG) & SaturateTactic(alphaRule) & proveOrRefuteAbs & DebuggingTactics.debug("...abs done", DEBUG)) | speculativeQENoAbs
  })

  /** QE with smart hiding. */
  private lazy val smartHideQE: BelleExpr =
    (DebuggingTactics.debug("Bound", DEBUG) & hideNonmatchingBounds & smartHide & QE & done) |
    (DebuggingTactics.debug("Non-Bound", DEBUG) & smartHide & QE & done)

  /** QE without handling abs */
  // was "QE"
  private lazy val speculativeQENoAbs: BelleExpr = anon ((_: Sequent) => {
    (DebuggingTactics.debug("Trying orIntro and smart hiding...", DEBUG) & orIntro(smartHideQE) & DebuggingTactics.debug("... orIntro and smart hiding successful", DEBUG)) |
    (DebuggingTactics.debug("orIntro failed, trying smart hiding...", DEBUG) & smartHideQE & DebuggingTactics.debug("...smart hiding successful", DEBUG)) |
    (DebuggingTactics.debug("All simplifications failed, falling back to ordinary QE", DEBUG) & QE & done)
  })

  /** Uses the disjunction introduction proof rule to prove a disjunctions by proving any 1 of the disjuncts. */
  def orIntro(finish: BelleExpr): BelleExpr = anon ((sequent: Sequent) => {
    def toSingleSucc(retain: Int): BelleExpr = {
      sequent.succ.indices.patch(retain, List.empty, 1).reverse.map(i => hideR(SuccPos(i))).reduceLeftOption[BelleExpr](_&_).getOrElse(skip)
    }
    //@todo CounterExample might provide insight on which of the formulas are needed
    sequent.succ.indices.map(toSingleSucc(_) & finish & done).reduceLeftOption[BelleExpr](_|_).getOrElse(skip)
  })

  /** Proves abs by trying to find contradictions; falls back to QE if contradictions fail */
  lazy val proveOrRefuteAbs: BelleExpr = anon ((sequent: Sequent) => {
    val symbols = (sequent.ante.flatMap(StaticSemantics.symbols) ++ sequent.succ.flatMap(StaticSemantics.symbols)).toSet
    if (symbols.contains(InterpretedSymbols.absF)) exhaustiveAbsSplit & OnAll((SaturateTactic(hideR('R)) & ToolTactics.assertNoCex & QE & done) | speculativeQENoAbs)
    else throw new TacticInapplicableFailure("Sequent does not contain abs")
  })

  /** Splits absolute value functions to create more, but hopefully simpler, goals. */
  // was "absSplit"
  // TODO: remove
  def exhaustiveAbsSplit: BelleExpr = anon ((sequent: Sequent) => {
    val absTerms = scala.collection.mutable.Set[Term]() // remember which abs are expanded already (absExp tactic expands same term everywhere)

    def absPos(fml: Formula): List[PosInExpr] = {
      val result = ListBuffer[PosInExpr]()
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, e: Term): Either[Option[StopTraversal], Term] = e match {
          case FuncOf(fn, _) if fn == InterpretedSymbols.absF =>
            if (!absTerms.contains(e)) {
              result += p
              absTerms.add(e)
            }
            Left(None)
          case _ => Left(None)
        }
      }, fml)
      result.toList
    }

    val anteAbs = sequent.ante.zipWithIndex.
      filter{ case (f,_) => StaticSemantics.symbols(f).contains(InterpretedSymbols.absF)}.
      map{ case (f, i) => (f, AntePosition.base0(i)) }
    val succAbs = sequent.succ.zipWithIndex.
      filter{ case (f,_) => StaticSemantics.symbols(f).contains(InterpretedSymbols.absF)}.
      map{ case (f,i) => (f, SuccPosition.base0(i)) }

    val absTactic = (anteAbs++succAbs).
      //@note p+inExpr navigates to sub-expression since p are top
      map({ case (f,p) => (f, absPos(f).sortBy(_.pos.length).reverse.map(inExpr => p ++ inExpr)) }).
      map({ case (_,p) => p.map(pos => OnAll(abs(pos) & orL('Llast))).reduceLeftOption[BelleExpr](_&_).getOrElse(skip) }).
        reduceLeftOption[BelleExpr](_&_).getOrElse(skip)

    absTactic & OnAll(SaturateTactic(andL('_))) & OnAll(SaturateTactic(exhaustiveEqL2R(hide=true)('L)))
  })

  /** Hides formulas with non-matching bounds. */
  def hideNonmatchingBounds: BelleExpr = anon ((sequent: Sequent) => {
    SignAnalysis.boundHideCandidates(sequent).sortBy(_.getIndex).reverse.map(hide(_)).reduceLeftOption[BelleExpr](_&_).getOrElse(skip)
  })

  def hideInconsistentSigns: BelleExpr = anon ((sequent: Sequent) => {
    SignAnalysis.signHideCandidates(sequent).sortBy(_.getIndex).reverse.map(hide(_)).reduceLeftOption[BelleExpr](_&_).getOrElse(skip)
  })

  /** Auto-transforms formulas from upper/lower bounds to concrete value (e.g., t<=ep, transform d>=A*ep to d>=A*t. */
  def autoMonotonicityTransform: BelleExpr = anon ((sequent: Sequent) => {
    //@todo "dependency" clustering and try to transform in a way that removes symbols from the sequent
    val signs = SignAnalysis.computeSigns(sequent)
    def transformOnConsistentSign(v: Variable, b: Term, i: Int) = {
      // transform only when v and b have consistent signs
      val vSigns = signs.get(v).map(_.keySet).getOrElse(Set.empty)
      val bSigns = signs.get(b).map(_.keySet).getOrElse(Set.empty)
      val canTransform = !vSigns.contains(Sign.Unknown) && vSigns.nonEmpty && bSigns.nonEmpty && vSigns.intersect(bSigns) == vSigns.union(bSigns)
      //@todo on unknown bounds, split into x<=0 | x>=0 and transform on subsequent branches?
      if (canTransform && StaticSemantics.symbols(b).size <= 1) Some(v -> b, i)
      else None
    }
    val varBounds = sequent.ante.zipWithIndex.flatMap({
      case (Equal(_, _), _) => None // QE handles equality rewriting
      case (NotEqual(_, _), _) => None
      case (c: ComparisonFormula, i) => (c.left, c.right) match {
        case (v: Variable, b: Term) => transformOnConsistentSign(v, b, i)
        case (b: Term, v: Variable) => transformOnConsistentSign(v, b, i)
        case _ => None
      }
      case _ => None
    })

    val bounds = varBounds.groupBy({ case (_, p) => p}).map({ case (k, v) => k->v.flatMap({ case ((v, b), _) => v :: b :: Nil }).toSet })
    // first transform formulas that use the bound (are not a bounds formula themselves)
    val transformUses = varBounds.map({
      case ((v: Variable, b: Term), _) =>
        val bs = StaticSemantics.symbols(b)
        sequent.ante.zipWithIndex.filter({ case (_, i) => !bounds.get(i).exists(_.contains(b)) }).
          map({ case (fml, i) => if (StaticSemantics.symbols(fml).intersect(bs).nonEmpty) Idioms.?(transformEquality(Equal(b, v))(AntePos(i))) else skip }).
          reduceLeftOption[BelleExpr](_ & _).getOrElse(skip)
    }).map(Idioms.?).reduceLeftOption[BelleExpr](_ & _).getOrElse(skip)
    // second transform the bounds formulas
    val transformBounds = varBounds.map({
      case ((v: Variable, b: Term), _) =>
        val bs = StaticSemantics.symbols(b)
        sequent.ante.zipWithIndex.filter({ case (_, i) => bounds.get(i).exists(_.contains(b)) }).
          map({ case (fml, i) => if (StaticSemantics.symbols(fml).intersect(bs).nonEmpty) Idioms.?(transformEquality(Equal(b, v))(AntePos(i))) else skip }).
          reduceLeftOption[BelleExpr](_ & _).getOrElse(skip)
    }).map(Idioms.?).reduceLeftOption[BelleExpr](_ & _).getOrElse(skip)
    transformUses & transformBounds
  })

}
