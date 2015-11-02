package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.pt.ProofTerm
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._

/**
 * [[ProofRuleTactics]] contains tactical implementations of the propositional sequent calculus
 * and other proof rules that are implemented by KeYmaera X.
 * @author Nathan Fulton
 */
object ProofRuleTactics {
  /**
   * Throw exception if there is more than one open subgoal on the provable.
   */
  private def requireOneSubgoal(provable: Provable) =
    if(provable.subgoals.length != 1) throw BelleError("Expected exactly one sequent in Provable")

  def cut(f: Formula) = new InputTactic[Formula](f) {
    override def computeExpr() = new BuiltInTactic(s"Cut(${input.prettyString})") {
      override def result(provable: Provable): Provable = {
        provable(core.Cut(input), 0)
      }
    }
  }

  def cutL(f: Formula) = new InputTactic[Formula](f) {
    override def computeExpr() = new BuiltInLeftTactic("CutL") {
      override def applyAt(provable: Provable, pos: AntePos): Provable = {
        requireOneSubgoal(provable)
        provable(core.CutLeft(f, pos), 0)
      }
    }
  }

  def cutR(f: Formula) = new InputTactic[Formula](f) {
    override def computeExpr() = new BuiltInRightTactic("CutR") {
      override def applyAt(provable: Provable, pos: SuccPos): Provable = {
        requireOneSubgoal(provable)
        provable(core.CutRight(f, pos), 0)
      }
    }
  }

  def cutLR(f: Formula) = new InputTactic[Formula](f) {
    override def computeExpr() = new BuiltInPositionTactic("CutR") {
      override def applyAt(provable: Provable, pos: SeqPos): Provable = {
        requireOneSubgoal(provable)
        if (pos.isAnte) provable(core.CutLeft(f, pos.asInstanceOf[AntePos]), 0)
        else provable(core.CutRight(f, pos.asInstanceOf[SuccPos]), 0)
      }
    }
  }

  def notL = new BuiltInLeftTactic("NotL") {
    override def applyAt(provable: Provable, pos: AntePos): Provable = {
      requireOneSubgoal(provable)
      provable(core.NotLeft(pos), 0)
    }
  }

  def notR = new BuiltInRightTactic("NotR") {
    override def applyAt(provable: Provable, pos: SuccPos): Provable = {
      requireOneSubgoal(provable)
      provable(core.NotRight(pos), 0)
    }
  }

  def andR = new BuiltInRightTactic("AndR") {
    override def applyAt(provable: Provable, pos : SuccPos) = {
      requireOneSubgoal(provable)
      provable(core.AndRight(pos), 0)
    }
  }

  def andL = new BuiltInLeftTactic("AndL") {
    override def applyAt(provable: Provable, pos: AntePos) = {
      requireOneSubgoal(provable)
      provable(core.AndLeft(pos), 0)
    }
  }

  def orR = new BuiltInRightTactic("OrR") {
    override def applyAt(provable: Provable, pos : SuccPos) = {
      requireOneSubgoal(provable)
      provable(core.OrRight(pos), 0)
    }
  }

  def orL = new BuiltInLeftTactic("OrL") {
    override def applyAt(provable: Provable, pos: AntePos) = {
      requireOneSubgoal(provable)
      provable(core.OrLeft(pos), 0)
    }
  }

  def implyR = new BuiltInRightTactic("ImplyR") {
    override def applyAt(provable : Provable, pos : SuccPos) = {
      requireOneSubgoal(provable)
      provable(core.ImplyRight(pos), 0)
    }
  }

  def implyL = new BuiltInLeftTactic("ImplyL") {
    override def applyAt(provable : Provable, pos: AntePos) = {
      requireOneSubgoal(provable)
      provable(core.ImplyLeft(pos), 0)
    }
  }

  def equivR = new BuiltInRightTactic("EquivR") {
    override def applyAt(provable: Provable, pos: SuccPos): Provable = {
      requireOneSubgoal(provable)
      provable(core.EquivRight(pos), 0)
    }
  }

  def equivL = new BuiltInLeftTactic("EquivL") {
    override def applyAt(provable: Provable, pos: AntePos): Provable = {
      requireOneSubgoal(provable)
      provable(core.EquivLeft(pos), 0)
    }
  }

  def commuteEquivL = new BuiltInLeftTactic("CommuteEquivL") {
    override def applyAt(provable: Provable, pos: AntePos): Provable = {
      requireOneSubgoal(provable)
      provable(core.CommuteEquivLeft(pos), 0)
    }
  }

  def commuteEquivR = new BuiltInRightTactic("CommuteEquivR") {
    override def applyAt(provable: Provable, pos: SuccPos): Provable = {
      requireOneSubgoal(provable)
      provable(core.CommuteEquivRight(pos), 0)
    }
  }

  def equivifyR = new BuiltInRightTactic("EquivifyR") {
    override def applyAt(provable: Provable, pos: SuccPos): Provable = {
      requireOneSubgoal(provable)
      provable(core.EquivifyRight(pos), 0)
    }
  }

  def hideL = new BuiltInLeftTactic("HideL") {
    override def applyAt(provable: Provable, pos: AntePos): Provable = {
      requireOneSubgoal(provable)
      provable(core.HideLeft(pos), 0)
    }
  }

  def hideR = new BuiltInRightTactic("HideR") {
    override def applyAt(provable: Provable, pos: SuccPos): Provable = {
      requireOneSubgoal(provable)
      provable(core.HideRight(pos), 0)
    }
  }

  def coHideL = new BuiltInLeftTactic("CoHideL") {
    override def applyAt(provable: Provable, pos: AntePos): Provable = {
      requireOneSubgoal(provable)
      provable(core.CoHideLeft(pos), 0)
    }
  }

  def coHideR = new BuiltInRightTactic("CoHideR") {
    override def applyAt(provable: Provable, pos: SuccPos): Provable = {
      requireOneSubgoal(provable)
      provable(core.CoHideRight(pos), 0)
    }
  }

  def coHide2 = new BuiltInTwoPositionTactic("CoHide2") {
    override def applyAt(provable: Provable, posOne: SeqPos, posTwo: SeqPos): Provable = {
      requireOneSubgoal(provable)
      require(posOne.isInstanceOf[AntePos] && posTwo.isInstanceOf[SuccPos], "Should take an antecedent and a succedent position.")
      provable(core.CoHide2(posOne.asInstanceOf[AntePos], posTwo.asInstanceOf[SuccPos]), 0)
    }
  }

  def exchangeL = new BuiltInTwoPositionTactic("ExchangeL") {
    override def applyAt(provable: Provable, posOne: SeqPos, posTwo: SeqPos): Provable = {
      requireOneSubgoal(provable)
      require(posOne.isAnte && posTwo.isAnte, "Both positions should be in the Antecedent.")
      provable(core.ExchangeLeftRule(posOne.asInstanceOf[AntePos], posTwo.asInstanceOf[AntePos]), 0)
    }
  }

  def exchangeR = new BuiltInTwoPositionTactic("ExchangeR") {
    override def applyAt(provable: Provable, posOne: SeqPos, posTwo: SeqPos): Provable = {
      requireOneSubgoal(provable)
      require(posOne.isSucc && posTwo.isSucc, "Both positions should be in the Succedent.")
      provable(core.ExchangeRightRule(posOne.asInstanceOf[SuccPos], posTwo.asInstanceOf[SuccPos]), 0)
    }
  }

  def US(subst: USubst, origin: Sequent) = new BuiltInTactic("US") {
    override def result(provable: Provable): Provable = {
      requireOneSubgoal(provable)
      provable(core.UniformSubstitutionRule(subst, origin), 0)
    }
  }

  def axiomatic(axiomName: String, subst: USubst) = new BuiltInTactic(s"US of Axiom ${axiomName}") {
    override def result(provable: Provable): Provable = {
      requireOneSubgoal(provable)
      provable(core.AxiomaticRule(axiomName, subst), 0)
    }
  }

  def uniformRenaming(what: Variable, repl: Variable) = new BuiltInTactic("UniformRenaming") {
    override def result(provable: Provable): Provable = {
      requireOneSubgoal(provable)
      provable(core.UniformRenaming(what, repl), 0)
    }
  }

  def boundRenaming(what: Variable, repl: Variable) = new BuiltInTactic("BoundRenaming") {
    override def result(provable: Provable): Provable = {
      requireOneSubgoal(provable)
      provable(core.BoundRenaming(what, repl), 0)
    }
  }

  def skolemize = new BuiltInPositionTactic("Skolemize") {
    override def applyAt(provable: Provable, pos: SeqPos): Provable = {
      requireOneSubgoal(provable)
      provable(core.Skolemize(pos), 0)
    }
  }

  def dualFree = new BuiltInRightTactic("DualFree") {
    override def applyAt(provable: Provable, pos: SuccPos): Provable = {
      requireOneSubgoal(provable)
      provable(core.DualFree(pos), 0)
    }
  }

  /** Closes a goal with exactly the form \phi |- \phi; i.e., no surrounding context. */
  def trivialCloser = new BuiltInTactic("CloseTrivialForm") {
    override def result(provable: Provable) = {
      requireOneSubgoal(provable)
      if(provable.subgoals.head.ante.length != 1 || provable.subgoals.head.succ.length != 1)
        throw BelleError(s"${this.name} should only be applied to formulas of the form \\phi |- \\phi")
      provable(core.Close(AntePos(0), SuccPos(0)), 0)
    }
  }

  /** Closes the goal using specified positions. */
  def close = new BuiltInTwoPositionTactic("Close") {
    override def applyAt(provable: Provable, posOne: SeqPos, posTwo: SeqPos): Provable = {
      requireOneSubgoal(provable)
      (posOne, posTwo) match {
        case (antePos : AntePos, succPos : SuccPos) => provable(core.Close(antePos, succPos), 0)
        case _ => throw BelleError("Close should receive a single antecedent position and a single succedent position.")
      }
    }
  }

  def closeTrue = new BuiltInRightTactic("CloseTrue") {
    override def applyAt(provable: Provable, pos: SuccPos): Provable = {
      requireOneSubgoal(provable)
      provable(core.CloseTrue(pos), 0)
    }
  }

  def closeFalse = new BuiltInLeftTactic("CloseFalse") {
    override def applyAt(provable: Provable, pos: AntePos): Provable = {
      requireOneSubgoal(provable)
      provable(core.CloseFalse(pos), 0)
    }
  }
}
