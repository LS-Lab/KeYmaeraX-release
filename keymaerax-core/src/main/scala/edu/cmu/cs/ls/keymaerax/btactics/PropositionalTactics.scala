package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._

import edu.cmu.cs.ls.keymaerax.core._
import Augmentors._

import scala.language.postfixOps

/**
 * [[PropositionalTactics]] provides tactics for propositional reasoning.
 */
object PropositionalTactics {
  /**
   * Inverse of [[ProofRuleTactics.implyR]].
   * {{{
   *   G, G' |- D, D', a -> b
   * -------------------------
   *   G, a, G' |- D, b, D'
   * }}}
   * @author Nathan Fulton
   * @author Stefan Mitsch
   * @see [[ProofRuleTactics.implyR]]
   * @see [[UnifyUSCalculus.implyRi]]
   */
  lazy val implyRi: DependentTactic = implyRi()
  def implyRi(antePos: AntePos = AntePos(0), succPos: SuccPos = SuccPos(0)): DependentTactic = new SingleGoalDependentTactic("inverse imply right") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      require(sequent.ante.length > antePos.getIndex && sequent.succ.length > succPos.getIndex,
        "Ante position " + antePos + " or succ position " + succPos + " is out of bounds; provable has ante size " +
          sequent.ante.length + " and succ size " + sequent.succ.length)
      val left = sequent.ante(antePos.getIndex)
      val right = sequent.succ(succPos.getIndex)
      val cutUsePos = AntePos(sequent.ante.length)
      cut(Imply(left, right)) <(
        /* use */ implyL(cutUsePos) & DoAll(TactixLibrary.close),
        /* show */ (assertE(right, "")(succPos) & hideR(succPos) & assertE(left, "")(antePos) & hideL(antePos)) partial /* This is the result. */)
    }
  }

  /**
   * Inverse of [[ProofRuleTactics.orR]].
   * {{{
   *   G |- D, D', D'', a | b
   * -------------------------
   *   G |- D, a, D', b, D''
   * }}}
   * @author Stefan Mitsch
   * @see [[ProofRuleTactics.orR]]
   */
  lazy val orRi: DependentTactic = orRi()
  def orRi(pos1: SuccPos = SuccPos(0), pos2: SuccPos = SuccPos(1)): DependentTactic = new SingleGoalDependentTactic("inverse or right") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      require(pos1 != pos2, "Two distinct positions required")
      require(sequent.succ.length > pos1.getIndex && sequent.succ.length > pos2.getIndex,
        "Position " + pos1 + " or position " + pos2 + " is out of bounds; provable has succ size " + sequent.succ.length)
      val left = sequent.succ(pos1.getIndex)
      val right = sequent.succ(pos2.getIndex)
      val cutUsePos = AntePos(sequent.ante.length)
      cut(Or(left, right)) <(
        /* use */ orL(cutUsePos) & DoAll(TactixLibrary.close),
        /* show */
          if (pos1.getIndex > pos2.getIndex) (assertE(left, "")(pos1) & hideR(pos1) & assertE(right, "")(pos2) & hideR(pos2)) partial
          else (assertE(right, "")(pos2) & hideR(pos2) & assertE(left, "")(pos1) & hideR(pos1)) partial
        )
    }
  }

  /**
   * Inverse of [[ProofRuleTactics.andL]].
   * {{{
   *   G, G', G'', a&b  |- D
   * -------------------------
   *   G, a, G', b, G'' |- D
   * }}}
   * @author Stefan Mitsch
   * @see [[ProofRuleTactics.andL]]
   */
  lazy val andLi: DependentTactic = implyRi()
  def andLi(pos1: AntePos = AntePos(0), pos2: AntePos = AntePos(1)): DependentTactic = new SingleGoalDependentTactic("inverse and left") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      require(pos1 != pos2, "Two distinct positions required")
      require(sequent.ante.length > pos1.getIndex && sequent.ante.length > pos2.getIndex,
        "Position " + pos1 + " or position " + pos2 + " is out of bounds; provable has ante size " + sequent.ante.length)
      val left = sequent.ante(pos1.getIndex)
      val right = sequent.ante(pos2.getIndex)
      val cutUsePos = SuccPos(sequent.succ.length)
      cut(And(left, right)) <(
        /* use */
          if (pos1.getIndex > pos2.getIndex) (assertE(left, "")(pos1) & hideL(pos1) & assertE(right, "")(pos2) & hideL(pos2)) partial
          else (assertE(right, "")(pos2) & hideL(pos2) & assertE(left, "")(pos1) & hideL(pos1)) partial,
        /* show */ andR(cutUsePos) & DoAll(TactixLibrary.close)
        )
    }
  }

  /**
   * Returns a tactic for propositional CE with purely propositional unpeeling. Useful when unpeeled fact is not
   * an equivalence, as needed by CE. May perform better than CE for small contexts.
   * @see [[UnifyUSCalculus.CMon(Context)]]
   * @see [[UnifyUSCalculus.CE(Context)]]
   * @example{{{
   *                  z=1 |- z>0
   *         --------------------------propCE(PosInExpr(1::Nil))
   *           x>0 -> z=1 |- x>0 -> z>0
   * }}}
   * @param at Points to the position to unpeel.
   * @return The tactic.
   */
  def propCMon(at: PosInExpr): DependentTactic = new SingleGoalDependentTactic("Prop. CMon") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      require(sequent.ante.length == 1 && sequent.succ.length == 1 &&
        sequent.ante.head.at(at)._1 == sequent.succ.head.at(at)._1, s"Propositional CMon requires single antecedent " +
        s"and single succedent formula with matching context to $at, but got $sequent")

      // we know that we have the same operator in antecedent and succedent with the same lhs -> we know that one
      // will branch and one of these branches will close by identity. on the other branch, we have to hide
      // list all cases explicitly, hide appropriate formulas in order to not blow up branching
      (((notL(-1) & notR(1) & assertT(1, 1) partial)
        | ((andL(-1) & andR(1) <((close | (hideL(-2) partial)) partial, (close | (hideL(-1) partial)) partial) & assertT(1, 1) partial)
        | ((orR(1) & orL(-1) <((close | (hideR(2) partial)) partial, (close | (hideR(1) partial)) partial) & assertT(1, 1) partial)
        | ((implyR(1) & implyL(-1) <((close | (hideR(1) partial)) partial, (close | (hideL(-1) partial)) partial) & assertT(1, 1) partial)
        | ((monb partial)
        | ((mond partial)
        | ((allR(1) & allL(-1) partial)
        | (existsL(-1) & existsR(1) partial)
        partial) partial) partial) partial) partial) partial) partial) partial)*at.pos.length
    }
  }

  /**
   * Modus ponens.
   * @example{{{
   *      p, q |-
   *   ------------ modusPonens
   *   p, p->q |-
   * }}}
   * @param assumption Position pointing to p
   * @param implication Position pointing to p->q
   * @return The tactic.
   */
  def modusPonens(assumption: AntePos, implication: AntePos): BelleExpr = new SingleGoalDependentTactic("Modus Ponens") {
    override def computeExpr(sequent: Sequent): BelleExpr = {
      val p = AntePos(assumption.getIndex - (if (assumption.getIndex > implication.getIndex) 1 else 0))
      //@todo adapt implyLOld to implyL
      implyLOld(implication) <(
        cohide2(p, SuccPos(sequent.succ.length)) & close,
        Idioms.ident
        )
    }
  }
}
