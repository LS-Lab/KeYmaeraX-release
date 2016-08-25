/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TacticFactory._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.core._

import scala.language.postfixOps

/**
  * Sequent Calculus for propositional and first-order logic.
  * @author Andre Platzer
  * @author Stefan Mitsch
  * @see [[SequentCalculus]]
  */
object SequentCalculus extends SequentCalculus

/**
  * Sequent Calculus for propositional and first-order logic.
  * @author Andre Platzer
  * @author Stefan Mitsch
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-008-9103-8 Differential dynamic logic for hybrid systems]]. Journal of Automated Reasoning, 41(2), pages 143-189, 2008.
  * @see [[edu.cmu.cs.ls.keymaerax.core.Rule]]
  */
trait SequentCalculus {

  //////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
  // Propositional tactics

  /** Hide/weaken whether left or right */
  val hide    : DependentPositionTactic = ProofRuleTactics.hide
  /** Hide/weaken left: weaken a formula to drop it from the antecedent ([[edu.cmu.cs.ls.keymaerax.core.HideLeft HideLeft]]) */
  val hideL   : BuiltInLeftTactic = "HideL" by { (pr:Provable, pos:AntePosition) => pr(HideLeft(pos.checkTop), 0) }
  /** Hide/weaken right: weaken a formula to drop it from the succcedent ([[edu.cmu.cs.ls.keymaerax.core.HideRight HideRight]]) */
  val hideR   : BuiltInRightTactic = "HideR" by { (pr:Provable, pos:SuccPosition) => pr(HideRight(pos.checkTop), 0) }
  /** CoHide/weaken left: drop all other formulas from the sequent ([[edu.cmu.cs.ls.keymaerax.core.CoHideLeft CoHideLeft]]) */
  val cohideL : BuiltInLeftTactic = "cohideL" by { (pr:Provable, pos:AntePosition) => pr(CoHideLeft(pos.checkTop), 0) }
  /** CoHide/weaken right: drop all other formulas from the sequent ([[edu.cmu.cs.ls.keymaerax.core.CoHideRight CoHideRight]]) */
  val cohideR : BuiltInRightTactic = "cohideR" by { (pr:Provable, pos:SuccPosition) => pr(CoHideRight(pos.checkTop), 0) }
  /** CoHide/coweaken whether left or right: drop all other formulas from the sequent ([[edu.cmu.cs.ls.keymaerax.core.CoHideLeft CoHideLeft]]) */
  lazy val cohide             : DependentPositionTactic = ProofRuleTactics.coHide
  /** CoHide2/coweaken2 both left and right: drop all other formulas from the sequent ([[edu.cmu.cs.ls.keymaerax.core.CoHide2 CoHide2]]) */
  def cohide2: BuiltInTwoPositionTactic = "CoHide2" by {(pr:Provable, ante: Position, succ: Position) => {
      require(ante.isAnte && succ.isSucc, "Expects an antecedent and a succedent position.")
      pr(CoHide2(ante.checkAnte.top, succ.checkSucc.top), 0)
    }
  }
  /** !L Not left: move an negation in the antecedent to the succedent ([[edu.cmu.cs.ls.keymaerax.core.NotLeft NotLeft]]) */
  val notL    : BuiltInLeftTactic = "notL" by { (pr:Provable, pos:AntePosition) => pr(NotLeft(pos.checkTop), 0) }
  /** !R Not right: move an negation in the succedent to the antecedent ([[edu.cmu.cs.ls.keymaerax.core.NotRight NotRight]]) */
  val notR    : BuiltInRightTactic = "notR" by { (pr:Provable, pos:SuccPosition) => pr(NotRight(pos.checkTop), 0) }
  /** &L And left: split a conjunction in the antecedent into separate assumptions ([[edu.cmu.cs.ls.keymaerax.core.AndLeft AndLeft]]) */
  val andL    : BuiltInLeftTactic = "andL" by { (pr:Provable, pos:AntePosition) => pr(AndLeft(pos.checkTop), 0) }
  /** Inverse of [[andL]].
    * {{{
    *   G, G', G'', a&b  |- D
    * -------------------------
    *   G, a, G', b, G'' |- D
    * }}}
    */
  def andLi(pos1: AntePos = AntePos(0), pos2: AntePos = AntePos(1)): DependentTactic = PropositionalTactics.andLi(pos1, pos2)
  lazy val andLi: DependentTactic = andLi()
  /** &R And right: prove a conjunction in the succedent on two separate branches ([[edu.cmu.cs.ls.keymaerax.core.AndRight AndRight]]) */
  val andR    : BuiltInRightTactic = "andR" by { (pr:Provable, pos:SuccPosition) => pr(AndRight(pos.checkTop), 0) }
  /** |L Or left: use a disjunction in the antecedent by assuming each option on separate branches ([[edu.cmu.cs.ls.keymaerax.core.OrLeft OrLeft]]) */
  val orL     : BuiltInLeftTactic = "orL" by { (pr:Provable, pos:AntePosition) => pr(OrLeft(pos.checkTop), 0) }
  /** Inverse of [[orR]].
    * {{{
    *   G |- D, D', D'', a | b
    * -------------------------
    *   G |- D, a, D', b, D''
    * }}}
    */
  def orRi(pos1: SuccPos = SuccPos(0), pos2: SuccPos = SuccPos(1)): DependentTactic = PropositionalTactics.orRi(pos1, pos2)
  lazy val orRi: DependentTactic = orRi()
  /** |R Or right: split a disjunction in the succedent into separate formulas to show alternatively ([[edu.cmu.cs.ls.keymaerax.core.OrRight OrRight]]) */
  val orR     : BuiltInRightTactic = "orR" by { (pr:Provable, pos:SuccPosition) => pr(OrRight(pos.checkTop), 0) }
  /** ->L Imply left: use an implication in the antecedent by proving its left-hand side on one branch and using its right-hand side on the other branch ([[edu.cmu.cs.ls.keymaerax.core.ImplyLeft ImplyLeft]]) */
  val implyL  : BuiltInLeftTactic = "implyL" by { (pr:Provable, pos:AntePosition) => pr(ImplyLeft(pos.checkTop), 0) }
  /** ->R Imply right: prove an implication in the succedent by assuming its left-hand side and proving its right-hand side ([[edu.cmu.cs.ls.keymaerax.core.ImplyRight ImplyRight]]) */
  val implyR  : BuiltInRightTactic = "implyR" by { (pr:Provable, pos:SuccPosition) => pr(ImplyRight(pos.checkTop), 0) }
  /** Inverse of [[implyR]].
    * {{{
    *   G, G' |- D, D', a -> b
    * -------------------------
    *   G, a, G' |- D, b, D'
    * }}}
    */
  def implyRi(antePos: AntePos = AntePos(0), succPos: SuccPos = SuccPos(0)): DependentTactic = PropositionalTactics.implyRi(antePos, succPos)
  lazy val implyRi: DependentTactic = implyRi()
  /** <->L Equiv left: use an equivalence by considering both true or both false cases ([[edu.cmu.cs.ls.keymaerax.core.EquivLeft EquivLeft]]) */
  val equivL  : BuiltInLeftTactic = "equivL" by { (pr:Provable, pos:AntePosition) => pr(EquivLeft(pos.checkTop), 0) }
  /** <->R Equiv right: prove an equivalence by proving both implications ([[edu.cmu.cs.ls.keymaerax.core.EquivRight EquivRight]]) */
  val equivR  : BuiltInRightTactic = "equivR" by { (pr:Provable, pos:SuccPosition) => pr(EquivRight(pos.checkTop), 0) }

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
    * Skolemization with bound renaming on demand.
    * @example{{{
    *     y>5   |- x^2>=0
    *     --------------------------allSkolemize(1)
    *     y>5   |- \forall x x^2>=0
    * }}}
    * @example Uniformly renames other occurrences of the quantified variable in the context on demand. {{{
    *     x_0>0 |- x^2>=0
    *     --------------------------allSkolemize(1)
    *     x>0   |- \forall x x^2>=0
    * }}}
    * @see [[edu.cmu.cs.ls.keymaerax.core.Skolemize]]
    */
  lazy val allR               : DependentPositionTactic = FOQuantifierTactics.allSkolemize
  /** all left: instantiate a universal quantifier for variable x in the antecedent by the concrete instance `term`. */
  def allL(x: Variable, inst: Term) : DependentPositionTactic = FOQuantifierTactics.allInstantiate(Some(x), Some(inst))
  /** all left: instantiate a universal quantifier in the antecedent by the concrete instance `term`. */
  def allL(inst: Term)              : DependentPositionTactic = FOQuantifierTactics.allInstantiate(None, Some(inst))
  /** all left: instantiate a universal quantifier in the antecedent by itself. */
  lazy val allL                     : DependentPositionTactic = FOQuantifierTactics.allInstantiate(None, None)
  /** all left: instantiate a universal quantifier in the antecedent by the term obtained from position `instPos`. */
  //@todo turn this into a more general function that obtains data from the sequent.
  def allLPos(instPos: Position)    : DependentPositionTactic = "all instantiate pos" by ((pos:Position, sequent:Sequent) => sequent.sub(instPos) match {
    case Some(t: Term) => allL(t)(pos)
  })
  /** exists left: Skolemize an existential quantifier in the antecedent by introducing a new name for the witness. */
  lazy val existsL                    : DependentPositionTactic = "existsL" by ((pos,seq) => FOQuantifierTactics.existsSkolemize(pos))
  /** exists right: instantiate an existential quantifier for x in the succedent by a concrete instance `inst` as a witness */
  def existsR(x: Variable, inst: Term): DependentPositionTactic = FOQuantifierTactics.existsInstantiate(Some(x), Some(inst))
  /** exists right: instantiate an existential quantifier in the succedent by a concrete instance `inst` as a witness */
  def existsR(inst: Term)             : DependentPositionTactic = FOQuantifierTactics.existsInstantiate(None, Some(inst))
  /** exists right: instantiate an existential quantifier for x in the succedent by itself as a witness */
  lazy val existsR                    : DependentPositionTactic = "existsR" by ((pos,seq) => FOQuantifierTactics.existsInstantiate(None, None)(pos))
  /** exists right: instantiate an existential quantifier in the succedent by a concrete term obtained from position `instPos`. */
  def existsRPos(instPos: Position)   : DependentPositionTactic = "exists instantiate pos" by ((pos:Position, sequent:Sequent) => sequent.sub(instPos) match {
    case Some(t: Term) => existsR(t)(pos)
  })


  // closing

  /** close: closes the branch when the same formula is in the antecedent and succedent or true or false close */
  lazy val close             : BelleExpr         = closeId | closeT | closeF
  /** close: closes the branch when the same formula is in the antecedent and succedent ([[edu.cmu.cs.ls.keymaerax.core.Close Close]]) */
  //@todo improve efficiency by avoiding the unnecessary cohide2 step
  //@todo compare with ProofRuleTactics.close
  def close(a: AntePos, s: SuccPos) : BelleExpr = //cohide2(a, s) & ProofRuleTactics.trivialCloser
    new BuiltInTactic("close") {
      override def result(provable: Provable) = {
        ProofRuleTactics.requireOneSubgoal(provable, "close(" + a + "," + s + ")")
        provable(Close(a, s), 0)
      }
    }
  def close(a: Int, s: Int)  : BelleExpr = close(Position(a).checkAnte.top, Position(s).checkSucc.top)
  /** closeId: closes the branch when the same formula is in the antecedent and succedent ([[edu.cmu.cs.ls.keymaerax.core.Close Close]]) */
  lazy val closeIdWith: DependentPositionTactic = new DependentPositionTactic("close id") {
    /** Create the actual tactic to be applied at position pos */
    override def factory(pos:Position): DependentTactic = new DependentTactic(name) {
      override def computeExpr(v : BelleValue): BelleExpr = v match {
        case BelleProvable(provable, _) =>
          require(provable.subgoals.size == 1, "Expects exactly 1 subgoal, but got " + provable.subgoals.size + " subgoals")
          val s = provable.subgoals.head
          pos.top match {
            case p@AntePos(_) => close(p, SuccPos(s.succ.indexOf(s(p))))
            case p@SuccPos(_) => close(AntePos(s.ante.indexOf(s(p))), p)
          }
      }
    }
  }
  //@note do not forward to closeIdWith (performance)
  lazy val closeId           : DependentTactic = new DependentTactic("closeId") {
    override def computeExpr(v : BelleValue): BelleExpr = v match {
      case BelleProvable(provable, _) =>
        require(provable.subgoals.size == 1, "Expects exactly 1 subgoal, but got " + provable.subgoals.size + " subgoals")
        val s = provable.subgoals.head
        val fmls = s.ante.intersect(s.succ)
        require(fmls.nonEmpty, "Expects same formula in antecedent and succedent. Found:\n" + s.prettyString)
        val fml = fmls.head
        close(AntePos(s.ante.indexOf(fml)), SuccPos(s.succ.indexOf(fml)))
    }
  }
  /** closeT: closes the branch when true is in the succedent ([[edu.cmu.cs.ls.keymaerax.core.CloseTrue CloseTrue]]) */
  lazy val closeT            : DependentTactic = new SingleGoalDependentTactic("closeTrue") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      require(sequent.succ.contains(True), "Expects true in succedent,\n\t but succedent " + sequent.succ + " does not contain true")
      ProofRuleTactics.closeTrue('R, True)
    }
  }
  /** closeF: closes the branch when false is in the antecedent ([[edu.cmu.cs.ls.keymaerax.core.CloseFalse CloseFalse]]) */
  lazy val closeF            : DependentTactic = new SingleGoalDependentTactic("closeFalse") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      require(sequent.ante.contains(False), "Expects false in antecedent,\n\t but antecedent " + sequent.ante + " does not contain false")
      ProofRuleTactics.closeFalse('L, False)
    }
  }

  // derived propositional

  /** Turn implication on the right into an equivalence, which is useful to prove by CE etc. ([[edu.cmu.cs.ls.keymaerax.core.EquivifyRight EquivifyRight]]) */
  val equivifyR: BuiltInRightTactic = "EquivifyR" by { (pr:Provable, pos:SuccPosition) => pr(EquivifyRight(pos.checkTop), 0) }
  /** Modus Ponens: p&(p->q) -> q.
    * @example{{{
    *      p, q, G |- D
    *   ---------------- modusPonens
    *   p, p->q, G |- D
    * }}}
    * @param assumption Position pointing to p
    * @param implication Position pointing to p->q
    */
  def modusPonens(assumption: AntePos, implication: AntePos): BelleExpr = PropositionalTactics.modusPonens(assumption, implication)
  /** Commute equivalence on the left [[edu.cmu.cs.ls.keymaerax.core.CommuteEquivLeft CommuteEquivLeft]] */
  val commuteEquivL: BuiltInLeftTactic = "CommuteEquivL" by { (pr:Provable, pos:AntePosition) => pr(CommuteEquivLeft(pos.checkTop), 0) }
  /** Commute equivalence on the right [[edu.cmu.cs.ls.keymaerax.core.CommuteEquivRight CommuteEquivRight]] */
  val commuteEquivR: BuiltInRightTactic = "CommuteEquivR" by { (pr:Provable, pos:SuccPosition) => pr(CommuteEquivRight(pos.checkTop), 0) }
  /** Commute equality `a=b` to `b=a` */
  lazy val commuteEqual       : DependentPositionTactic = useAt("= commute")

}
