package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProofTerm
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
 * [[PropositionalTactics]] contains tactical implementations of the propositional sequent calculus.
 * @author Nathan Fulton
 */
object PropositionalTactics {
  /**
   * Throw exception if there is more than one open subgoal on the provable.
   */
  private def checkProvableShape(provable: Provable) =
    if(provable.subgoals.length != 1) throw BelleError("Expected exactly one sequent in Provable")

  def AndR = new BuiltInRightTactic("AndR") {
    override def applyAt(provable: Provable, pos : SuccPos) = {
      checkProvableShape(provable)
      provable(core.AndRight(pos), 0)
    }
  }

  def AndL = new BuiltInLeftTactic("AndL") {
    override def applyAt(provable: Provable, pos: AntePos) = {
      checkProvableShape(provable)
      provable(core.AndLeft(pos), 0)
    }
  }

  def OrR = new BuiltInRightTactic("OrR") {
    override def applyAt(provable: Provable, pos : SuccPos) = {
      checkProvableShape(provable)
      provable(core.OrRight(pos), 0)
    }
  }

  def OrL = new BuiltInLeftTactic("OrL") {
    override def applyAt(provable: Provable, pos: AntePos) = {
      checkProvableShape(provable)
      provable(core.OrLeft(pos), 0)
    }
  }

  def ImplyR = new BuiltInRightTactic("ImplyR") {
    override def applyAt(provable : Provable, pos : SuccPos) = {
      checkProvableShape(provable)
      provable(core.ImplyRight(pos), 0)
    }
  }

  def ImplyL = new BuiltInLeftTactic("ImplyL") {
    override def applyAt(provable : Provable, pos: AntePos) = {
      checkProvableShape(provable)
      provable(core.ImplyLeft(pos), 0)
    }
  }

  /** Closes a goal with exactly the form \phi |- \phi; i.e., no surrounding context. */
  def TrivialCloser = new BuiltInTactic("CloseTrivialForm") {
    override def result(provable: Provable) = {
      checkProvableShape(provable)
      if(provable.subgoals.head.ante.length != 1 || provable.subgoals.head.succ.length != 1)
        throw BelleError(s"${this.name} should only be applied to formulas of the form \\phi |- \\phi")
      provable(core.Close(AntePos(0), SuccPos(0)), 0)
    }
  }

  /** Closes the goal using specified positions. */
  def Close = new BuiltInTwoPositionTactic("Close") {
    override def applyAt(provable: Provable, posOne: SeqPos, posTwo: SeqPos): Provable = {
      checkProvableShape(provable)
      (posOne, posTwo) match {
        case (antePos : AntePos, succPos : SuccPos) => provable(core.Close(antePos, succPos), 0)
        case _ => throw BelleError("Close should receive a single antecedent position and a single succedent position.")
      }
    }
  }
}
