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
  private def checkProvableShape(provable: Provable) =
    if(provable.subgoals.length != 1) throw BelleError("Expected exactly one sequent in Provable")

  def AndR = new BuiltInRightTactic("AndR") {
    override def apply(provable: Provable, pos : SuccPos) = {
      checkProvableShape(provable)
      provable(core.AndRight(pos), 0)
    }
  }

  def AndL = new BuiltInLeftTactic("AndL") {
    override def apply(provable: Provable, pos: AntePos) = {
      checkProvableShape(provable)
      provable(core.AndLeft(pos), 0)
    }
  }

  def OrR = new BuiltInRightTactic("OrR") {
    override def apply(provable: Provable, pos : SuccPos) = {
      checkProvableShape(provable)
      provable(core.OrRight(pos), 0)
    }
  }

  def OrL = new BuiltInLeftTactic("OrL") {
    override def apply(provable: Provable, pos: AntePos) = {
      checkProvableShape(provable)
      provable(core.OrLeft(pos), 0)
    }
  }

  def ImplyR = new BuiltInRightTactic("ImplyR") {
    override def apply(provable : Provable, pos : SuccPos) = {
      checkProvableShape(provable)
      provable(core.ImplyRight(pos), 0)
    }
  }

  def ImplyL = new BuiltInLeftTactic("ImplyL") {
    override def apply(provable : Provable, pos: AntePos) = {
      checkProvableShape(provable)
      provable(core.ImplyLeft(pos), 0)
    }
  }

  
}
