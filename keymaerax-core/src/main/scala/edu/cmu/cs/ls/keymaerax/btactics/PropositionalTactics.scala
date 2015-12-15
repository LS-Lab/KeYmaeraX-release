package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.DebuggingTactics.{assert, debug}
import edu.cmu.cs.ls.keymaerax.btactics.DLTactics._
import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics._

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.tactics.PosInExpr

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
   */
  lazy val implyRi: DependentTactic = implyRi()
  def implyRi(antePos: AntePos = AntePos(0), succPos: SuccPos = SuccPos(0)): DependentTactic = new DependentTactic("inverse imply right") {
    override def computeExpr(v: BelleValue): BelleExpr = v match {
      case BelleProvable(provable) =>
        require(provable.subgoals.size == 1, "Provable must have only 1 subgoal, but has " + provable.subgoals.size)
        val sequent = provable.subgoals.head
        require(sequent.ante.length > antePos.getIndex && sequent.succ.length > succPos.getIndex,
          "Ante position " + antePos + " or succ position " + succPos + " is out of bounds; provable has ante size " +
            sequent.ante.length + " and succ size " + sequent.succ.length)
        val left = sequent.ante(antePos.getIndex)
        val right = sequent.succ(succPos.getIndex)
        val cutUsePos = AntePos(sequent.ante.length)
        cut(Imply(left, right)) <(
          /* use */ implyL(cutUsePos) & DoAll(TactixLibrary.close),
          /* show */ (assert(right, "")(succPos) & hideR(succPos) & assert(left, "")(antePos) & hideL(antePos)) partial /* This is the result. */)
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
  def propCMon(at: PosInExpr): DependentTactic = new DependentTactic("Prop. CMon") {
    //@todo would want to use result symbol of skolemizeT, for now we have to guess it
    def instWithGuessedSkolem(pos: SeqPos) = new DependentTactic("Instantiate with guessed skolem") {
      override def computeExpr(bv: BelleValue): BelleExpr = bv match {
        case BelleProvable(provable) =>
          require(provable.subgoals.size == 1)
          val s = provable.subgoals.head
          require(s(pos) match {
            case Forall(_ :: Nil, _) =>  pos.isAnte
            case Exists(_ :: Nil, _) => !pos.isAnte
            case _ => false
          })
          s(pos) match {
            case Forall(v :: Nil, _) if  pos.isAnte => ??? //@todo instantiateT(v, Variable(v.name, v.index match { case None => Some(0) case Some(i) => Some(i + 1) }, v.sort))(pos)
            case Exists(v :: Nil, _) if !pos.isAnte => ??? //@todo instantiateT(v, Variable(v.name, v.index match { case None => Some(0) case Some(i) => Some(i + 1) }, v.sort))(pos)
          }
      }
    }

    override def computeExpr(v: BelleValue): BelleExpr = v match {
      case BelleProvable(provable) =>
        require(provable.subgoals.size == 1, "Expected single sub goal, but got " + provable.subgoals.size)
        val sequent = provable.subgoals.head
        require(sequent.ante.length == 1 && sequent.succ.length == 1 &&
          sequent.ante.head.at(at)._1 == sequent.succ.head.at(at)._1, "")

        // we know that we have the same operator in antecedent and succedent with the same lhs -> we know that one
        // will branch and one of these branches will close by identity. on the other branch, we have to hide
        debug(s"Start unpeeling towards $at") &
        // list all cases explicitly, hide appropriate formulas in order to not blow up branching
        (((notL(AntePos(0)) & notR(SuccPos(0)) & assert(1, 1)) |
          (andL(AntePos(0)) & andR(SuccPos(0)) <(close | hideL(AntePos(1)), close | hideL(AntePos(0))) & assert(1, 1)) |
          (orR(SuccPos(0)) & orL(AntePos(0)) <(close | hideR(SuccPos(1)), close | hideR(SuccPos(0))) & assert(1, 1)) |
          (implyR(SuccPos(0)) & implyL(AntePos(0)) <(close | hideR(SuccPos(0)), close | hideL(AntePos(0))) & assert(1, 1)) |
          monb | mond |
          (skolemize(SuccPos(0)) & instWithGuessedSkolem(AntePos(0))) |
          (skolemize(AntePos(0)) & instWithGuessedSkolem(SuccPos(0)))
          ) & debug("Unpeeled one layer"))*at.pos.length & debug("Unpeeling finished")
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
  def modusPonens(assumption: AntePos, implication: AntePos): BelleExpr = new DependentTactic("Modus Ponens") {
    override def computeExpr(v: BelleValue): BelleExpr = v match {
      case BelleProvable(provable) =>
        require(provable.subgoals.size == 1, "Exactly one subgoal expected")
        val p = AntePos(assumption.getIndex - (if (assumption.getIndex > implication.getIndex) 1 else 0))
        implyL(implication) <(
          coHide2(p, SuccPos(provable.subgoals.head.seq.succ.length)) & trivialCloser,
          /*hideL(p)*/Idioms.ident partial
          )
    }
  }
}
