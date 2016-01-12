/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core._

import scala.language.postfixOps

/**
  * Sequent Calculus for propositional and first-order logic.
  * @author Andre Platzer
  * @author Stefan Mitsch
  * @see [[SequentCalculi]]
  */
object SequentCalculus extends SequentCalculi

/**
  * Sequent Calculus for propositional and first-order logic.
  * @author Andre Platzer
  * @author Stefan Mitsch
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-008-9103-8 Differential dynamic logic for hybrid systems]]. Journal of Automated Reasoning, 41(2), pages 143-189, 2008.
  * @see [[edu.cmu.cs.ls.keymaerax.core.Rule]]
  */
trait SequentCalculi {

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Propositional tactics

  /** Hide/weaken whether left or right */
  lazy val hide               : DependentPositionTactic = ProofRuleTactics.hide
  /** Hide/weaken given formula at given position */
//  def hide(fml: Formula): DependentPositionTactic = new DependentPositionTactic("hide") {
//    override def factory(pos: Position): DependentTactic = new DependentTactic(name) {
//      override def computeExpr(v: BelleValue): BelleExpr = assertE(fml, "hiding")(pos) & ProofRuleTactics.hide(pos)
//    }
//  }
  /** Hide/weaken left: weaken a formula to drop it from the antecedent ([[edu.cmu.cs.ls.keymaerax.core.HideLeft HideLeft]]) */
  lazy val hideL              : BuiltInLeftTactic = ProofRuleTactics.hideL
  /** Hide/weaken right: weaken a formula to drop it from the succcedent ([[edu.cmu.cs.ls.keymaerax.core.HideRight HideRight]]) */
  lazy val hideR              : BuiltInRightTactic = ProofRuleTactics.hideR
  /** CoHide/coweaken whether left or right: drop all other formulas from the sequent ([[edu.cmu.cs.ls.keymaerax.core.CoHideLeft CoHideLeft]]) */
  lazy val cohide             : DependentPositionTactic = ProofRuleTactics.coHide
  /** CoHide/coweaken whether left or right: drop all other formulas from the sequent ([[edu.cmu.cs.ls.keymaerax.core.CoHideLeft CoHideLeft]]) */
  //def cohide(fml: Formula)    : BelleExpr = DebuggingTactics.assert(fml, "cohiding") & cohide
  /** CoHide2/coweaken2 both left and right: drop all other formulas from the sequent ([[edu.cmu.cs.ls.keymaerax.core.CoHide2 CoHide2]]) */
  def cohide2: BuiltInTwoPositionTactic = ProofRuleTactics.coHide2
  /** !L Not left: move an negation in the antecedent to the succedent ([[edu.cmu.cs.ls.keymaerax.core.NotLeft NotLeft]]) */
  lazy val notL               : BuiltInLeftTactic = ProofRuleTactics.notL
  /** !R Not right: move an negation in the succedent to the antecedent ([[edu.cmu.cs.ls.keymaerax.core.NotRight NotRight]]) */
  lazy val notR               : BuiltInRightTactic = ProofRuleTactics.notR
  /** &L And left: split a conjunction in the antecedent into separate assumptions ([[edu.cmu.cs.ls.keymaerax.core.AndLeft AndLeft]]) */
  lazy val andL               : BuiltInLeftTactic = ProofRuleTactics.andL
  /** Inverse of andL */
  def andLi(pos1: AntePos = AntePos(0), pos2: AntePos = AntePos(1)): DependentTactic = PropositionalTactics.andLi(pos1, pos2)
  lazy val andLi: DependentTactic = andLi()
  /** &R And right: prove a conjunction in the succedent on two separate branches ([[edu.cmu.cs.ls.keymaerax.core.AndRight AndRight]]) */
  lazy val andR               : BuiltInRightTactic = ProofRuleTactics.andR
  /** |L Or left: use a disjunction in the antecedent by assuming each option on separate branches ([[edu.cmu.cs.ls.keymaerax.core.OrLeft OrLeft]]) */
  lazy val orL                : BuiltInLeftTactic = ProofRuleTactics.orL
  /** Inverse of orR */
  def orRi(pos1: SuccPos = SuccPos(0), pos2: SuccPos = SuccPos(1)): DependentTactic = PropositionalTactics.orRi(pos1, pos2)
  lazy val orRi: DependentTactic = orRi()
  /** |R Or right: split a disjunction in the succedent into separate formulas to show alternatively ([[edu.cmu.cs.ls.keymaerax.core.OrRight OrRight]]) */
  lazy val orR                : BuiltInRightTactic = ProofRuleTactics.orR
  /** ->L Imply left: use an implication in the antecedent by proving its left-hand side on one branch and using its right-hand side on the other branch ([[edu.cmu.cs.ls.keymaerax.core.ImplyLeft ImplyLeft]]) */
  lazy val implyL             : BuiltInLeftTactic = ProofRuleTactics.implyL
  /** ->R Imply right: prove an implication in the succedent by assuming its left-hand side and proving its right-hand side ([[edu.cmu.cs.ls.keymaerax.core.ImplyRight ImplyRight]]) */
  lazy val implyR             : BuiltInRightTactic = ProofRuleTactics.implyR
  /** Inverse of implyR */
  def implyRi(antePos: AntePos = AntePos(0), succPos: SuccPos = SuccPos(0)): DependentTactic = PropositionalTactics.implyRi(antePos, succPos)
  lazy val implyRi: DependentTactic = implyRi()
  /** <->L Equiv left: use an equivalence by considering both true or both false cases ([[edu.cmu.cs.ls.keymaerax.core.EquivLeft EquivLeft]]) */
  lazy val equivL             : BuiltInLeftTactic = ProofRuleTactics.equivL
  /** <->R Equiv right: prove an equivalence by proving both implications ([[edu.cmu.cs.ls.keymaerax.core.EquivRight EquivRight]]) */
  lazy val equivR             : BuiltInRightTactic = ProofRuleTactics.equivR

  /** cut a formula in to prove it on one branch and then assume it on the other. Or to perform a case distinction on whether it holds ([[edu.cmu.cs.ls.keymaerax.core.Cut Cut]]) */
  def cut(cut : Formula)      : InputTactic[Formula]         = ProofRuleTactics.cut(cut)
  /** cut a formula in in place of pos on the right to prove it on one branch and then assume it on the other. ([[edu.cmu.cs.ls.keymaerax.core.CutRight CutRight]]) */
  def cutR(cut : Formula)     : (SuccPos => InputTactic[Formula])  = ProofRuleTactics.cutR(cut)
  /** cut a formula in in place of pos on the left to prove it on one branch and then assume it on the other. ([[edu.cmu.cs.ls.keymaerax.core.CutLeft CutLeft]]) */
  def cutL(cut : Formula)     : (AntePos => InputTactic[Formula])  = ProofRuleTactics.cutL(cut)
  /** cut a formula in in place of pos to prove it on one branch and then assume it on the other (whether pos is left or right). ([[edu.cmu.cs.ls.keymaerax.core.CutLeft CutLeft]] or [[edu.cmu.cs.ls.keymaerax.core.CutRight CutRight]]) */
  def cutLR(cut : Formula)    : (Position => InputTactic[Formula])  = ProofRuleTactics.cutLR(cut)

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // First-order tactics

  // quantifiers
  /** all right: Skolemize a universal quantifier in the succedent ([[edu.cmu.cs.ls.keymaerax.core.Skolemize Skolemize]])
    * @see [[edu.cmu.cs.ls.keymaerax.core.Skolemize]]
    * @see [[edu.cmu.cs.ls.keymaerax.btactics.FOQuantifierTactics.allSkolemize]] */
  lazy val allR               : DependentPositionTactic = FOQuantifierTactics.allSkolemize
  /** all left: instantiate a universal quantifier in the antecedent by a concrete instance */
  def allL(x: Variable, inst: Term) : DependentPositionTactic = FOQuantifierTactics.allInstantiate(Some(x), Some(inst))
  def allL(inst: Term)              : DependentPositionTactic = FOQuantifierTactics.allInstantiate(None, Some(inst))
  lazy val allL                     : DependentPositionTactic = FOQuantifierTactics.allInstantiate(None, None)
  /** exists left: Skolemize an existential quantifier in the antecedent */
  lazy val existsL            : DependentPositionTactic = FOQuantifierTactics.existsSkolemize
  /** exists right: instantiate an existential quantifier in the succedent by a concrete instance as a witness */
  def existsR(x: Variable, inst: Term): DependentPositionTactic = FOQuantifierTactics.existsInstantiate(Some(x), Some(inst))
  def existsR(inst: Term)             : DependentPositionTactic = FOQuantifierTactics.existsInstantiate(None, Some(inst))
  lazy val existsR                    : DependentPositionTactic = FOQuantifierTactics.existsInstantiate(None, None)

  // closing

  /** close: closes the branch when the same formula is in the antecedent and succedent or true or false close */
  lazy val close             : BelleExpr         = closeId | closeT | closeF
  /** close: closes the branch when the same formula is in the antecedent and succedent ([[edu.cmu.cs.ls.keymaerax.core.Close Close]]) */
  def close(a: AntePosition, s: SuccPosition) : BelleExpr = cohide2(a, s) & ProofRuleTactics.trivialCloser
  def close(a: Int, s: Int)  : BelleExpr = close(Position(a).asInstanceOf[AntePosition], Position(s).asInstanceOf[SuccPosition])
  /** closeId: closes the branch when the same formula is in the antecedent and succedent ([[edu.cmu.cs.ls.keymaerax.core.Close Close]]) */
  lazy val closeId           : DependentTactic = new DependentTactic("close id") {
    override def computeExpr(v : BelleValue): BelleExpr = v match {
      case BelleProvable(provable, _) =>
        require(provable.subgoals.size == 1, "Expects exactly 1 subgoal, but got " + provable.subgoals.size + " subgoals")
        val s = provable.subgoals.head
        require(s.ante.intersect(s.succ).nonEmpty, "Expects same formula in antecedent and succedent,\n\t but antecedent " + s.ante + "\n\t does not overlap with succedent " + s.succ)
        val fml = s.ante.intersect(s.succ).head
        close(AntePosition.base0(s.ante.indexOf(fml)), SuccPosition.base0(s.succ.indexOf(fml)))
    }
  }
  /** closeT: closes the branch when true is in the succedent ([[edu.cmu.cs.ls.keymaerax.core.CloseTrue CloseTrue]]) */
  lazy val closeT            : DependentTactic = new SingleGoalDependentTactic("close true") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      require(sequent.succ.contains(True), "Expects true in succedent,\n\t but succedent " + sequent.succ + " does not contain true")
      ProofRuleTactics.closeTrue('R, True)
    }
  }
  /** closeF: closes the branch when false is in the antecedent ([[edu.cmu.cs.ls.keymaerax.core.CloseFalse CloseFalse]]) */
  lazy val closeF            : DependentTactic = new SingleGoalDependentTactic("close false") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      require(sequent.ante.contains(False), "Expects false in antecedent,\n\t but antecedent " + sequent.ante + " does not contain false")
      ProofRuleTactics.closeFalse('L, False)
    }
  }

  // derived propositional

  /** Turn implication on the right into an equivalence, which is useful to prove by CE etc. ([[edu.cmu.cs.ls.keymaerax.core.EquivifyRight EquivifyRight]]) */
  lazy val equivifyR          : BuiltInRightTactic = ProofRuleTactics.equivifyR
  /** Modus Ponens: p&(p->q) -> q */
  def modusPonens(assumption: AntePos, implication: AntePos): BelleExpr = PropositionalTactics.modusPonens(assumption, implication)
  /** Commute equivalence on the left [[edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics.commuteEquivL]] */
  lazy val commuteEquivL      : BuiltInLeftTactic = ProofRuleTactics.commuteEquivL
  /** Commute equivalence on the right [[edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics.commuteEquivR]] */
  lazy val commuteEquivR      : BuiltInRightTactic = ProofRuleTactics.commuteEquivR
  /** Commute equality */
  lazy val commuteEqual       : DependentPositionTactic = useAt("= commute")


  @deprecated("Use implyL instead.")
  private[btactics] lazy val implyLOld : BuiltInLeftTactic = ProofRuleTactics.implyLOld

}
