/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core.{Term, Variable, Formula}
import edu.cmu.cs.ls.keymaerax.tactics.Tactics.PositionTactic

/**
 * Hilbert Calculus for differential dynamic logic.
 * @author Andre Platzer
 * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
 * @todo add step tactic that uses the right useAt per operator.
 */
object HilbertCalculus {
  import TactixLibrary.useAt
//  // modalities
  /** assignb: [:=] simplify assignment by substitution or equation */
  lazy val assignb            : PositionTactic = useAt("[:=] assign equational") //@todo or "[:=] assign" if no clash
  /** randomb: [:*] simplify nondeterministic assignment to universal quantifier */
  lazy val randomb            : PositionTactic = useAt("[:*] assign nondet")
  /** testb: [?] simplifies test to an implication */
  lazy val testb              : PositionTactic = useAt("[?] test")
  /** diffSolve: solve a differential equation */
  def diffSolve               : PositionTactic = TacticLibrary.diffSolutionT
  /** choiceb: [++] handles both cases of a nondeterministic choice separately */
  lazy val choiceb            : PositionTactic = useAt("[++] choice")
  /** composeb: [;] handle both parts of a sequential composition one at a time */
  lazy val composeb           : PositionTactic = useAt("[;] compose")
  /** iterateb: [*] prove a property of a loop by unrolling it once */
  lazy val iterateb           : PositionTactic = useAt("[*] iterate")
//  /** I: prove a property of a loop by induction with the given loop invariant (hybrid systems) */
//  def I(invariant : Formula)  : PositionTactic = TacticLibrary.inductionT(Some(invariant))
//  def loop(invariant: Formula) = I(invariant)
//  /** K: modal modus ponens (hybrid systems) */
//  def K                       : PositionTactic = PropositionalTacticsImpl.kModalModusPonensT
//  /** V: vacuous box will be discarded (unless it changes values of the postcondition) (hybrid systems) */
//  def V                       : PositionTactic = HybridProgramTacticsImpl.boxVacuousT
//
//  // differential equations
  /** DW: Differential Weakening to use evolution domain constraint (equivalence form) */
  lazy val DW                 : PositionTactic = useAt("DW differential weakening")
//  /** DC: Differential Cut a new invariant for a differential equation */
//  def DC(invariant: Formula)  : PositionTactic = TacticLibrary.diffCutT(invariant)
  /** DE: Differential Effect exposes the effect of a differential equation on its differential symbols */
  lazy val DE                 : PositionTactic = ODETactics.diffEffectT
//  /** DI: Differential Invariant proves a formula to be an invariant of a differential equation */
//  def DI                      : PositionTactic = TacticLibrary.diffInvariant
//  /** DG: Differential Ghost add auxiliary differential equations with extra variables y'=a*y+b */
//  def DG(y:Variable, a:Term, b:Term) : PositionTactic = ODETactics.diffAuxiliaryT(y,a,b)
//  /** DA: Differential Ghost add auxiliary differential equations with extra variables y'=a*y+b and replacement formula */
//  def DA(y:Variable, a:Term, b:Term, r:Formula) : PositionTactic = ODETactics.diffAuxiliariesRule(y,a,b,r)
//  /** DS: Differential Solution solves a differential equation */
//  def DS                      : PositionTactic = ???
  /** Dassignb: Substitute a differential assignment */
  lazy val Dassignb           : PositionTactic = useAt("[':=] differential assign")
  /** Dplus: +' derives a sum */
  lazy val Dplus              : PositionTactic = useAt("+' derive sum")
  /** neg: -' derives neg */
  lazy val Dneg               : PositionTactic = useAt("-' derive neg")
  /** Dminus: -' derives a difference */
  lazy val Dminus             : PositionTactic = useAt("-' derive minus")
  /** Dtimes: *' derives a product */
  lazy val Dtimes             : PositionTactic = useAt("*' derive product")
  /** Dquotient: /' derives a quotient */
  lazy val Dquotient          : PositionTactic = useAt("/' derive quotient")
  /** Dpower: ^' derives a power */
  lazy val Dpower             : PositionTactic = useAt("^' derive power", PosInExpr(1::0::Nil))
  /** Dcompose: o' derives a function composition by chain rule */
  //lazy val Dcompose           : PositionTactic = ???

}
