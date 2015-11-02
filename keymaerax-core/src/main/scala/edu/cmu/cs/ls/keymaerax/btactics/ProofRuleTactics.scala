package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.Position


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

  def Cut(f: Formula) = new InputTactic[Formula](f) {
    override def computeExpr() = new BuiltInTactic(s"Cut(${input.prettyString})") {
      override def result(provable: Provable): Provable = {
        provable(core.Cut(input), 0)
      }
    }
  }

  def CutL(f: Formula) = new InputTactic[Formula](f) {
    override def computeExpr() = new BuiltInLeftTactic("CutL") {
      override def applyAt(provable: Provable, pos: AntePos): Provable = {
        requireOneSubgoal(provable)
        provable(core.CutLeft(f, pos), 0)
      }
    }
  }

  def CutR(f: Formula) = new InputTactic[Formula](f) {
    override def computeExpr() = new BuiltInRightTactic("CutR") {
      override def applyAt(provable: Provable, pos: SuccPos): Provable = {
        requireOneSubgoal(provable)
        provable(core.CutRight(f, pos), 0)
      }
    }
  }

  def CutLR(f: Formula) = new InputTactic[Formula](f) {
    override def computeExpr() = new BuiltInPositionTactic("CutLR") {
      override def applyAt(provable: Provable, pos: Position): Provable = {
        requireOneSubgoal(provable)
        if (pos.isAnte) provable(core.CutLeft(f, pos), 0)
        else provable(core.CutRight(f, pos), 0)
      }
    }
  }

  def NotL = new BuiltInLeftTactic("NotL") {
    override def applyAt(provable: Provable, pos: AntePos): Provable = {
      requireOneSubgoal(provable)
      provable(core.NotLeft(pos), 0)
    }
  }

  def NotR = new BuiltInRightTactic("NotR") {
    override def applyAt(provable: Provable, pos: SuccPos): Provable = {
      requireOneSubgoal(provable)
      provable(core.NotRight(pos), 0)
    }
  }

  def AndR = new BuiltInRightTactic("AndR") {
    override def applyAt(provable: Provable, pos : SuccPos) = {
      requireOneSubgoal(provable)
      provable(core.AndRight(pos), 0)
    }
  }

  def AndL = new BuiltInLeftTactic("AndL") {
    override def applyAt(provable: Provable, pos: AntePos) = {
      requireOneSubgoal(provable)
      provable(core.AndLeft(pos), 0)
    }
  }

  def OrR = new BuiltInRightTactic("OrR") {
    override def applyAt(provable: Provable, pos : SuccPos) = {
      requireOneSubgoal(provable)
      provable(core.OrRight(pos), 0)
    }
  }

  def OrL = new BuiltInLeftTactic("OrL") {
    override def applyAt(provable: Provable, pos: AntePos) = {
      requireOneSubgoal(provable)
      provable(core.OrLeft(pos), 0)
    }
  }

  def ImplyR = new BuiltInRightTactic("ImplyR") {
    override def applyAt(provable : Provable, pos : SuccPos) = {
      requireOneSubgoal(provable)
      provable(core.ImplyRight(pos), 0)
    }
  }

  def ImplyL = new BuiltInLeftTactic("ImplyL") {
    override def applyAt(provable : Provable, pos: AntePos) = {
      requireOneSubgoal(provable)
      provable(core.ImplyLeft(pos), 0)
    }
  }

  def EquivR = new BuiltInRightTactic("EquivR") {
    override def applyAt(provable: Provable, pos: SuccPos): Provable = {
      requireOneSubgoal(provable)
      provable(core.EquivRight(pos), 0)
    }
  }

  def EquivL = new BuiltInLeftTactic("EquivL") {
    override def applyAt(provable: Provable, pos: AntePos): Provable = {
      requireOneSubgoal(provable)
      provable(core.EquivLeft(pos), 0)
    }
  }

  def CommuteEquivL = new BuiltInLeftTactic("CommuteEquivL") {
    override def applyAt(provable: Provable, pos: AntePos): Provable = {
      requireOneSubgoal(provable)
      provable(core.CommuteEquivLeft(pos), 0)
    }
  }

  def CommuteEquivR = new BuiltInRightTactic("CommuteEquivR") {
    override def applyAt(provable: Provable, pos: SuccPos): Provable = {
      requireOneSubgoal(provable)
      provable(core.CommuteEquivRight(pos), 0)
    }
  }

  def EquivifyR = new BuiltInRightTactic("EquivifyR") {
    override def applyAt(provable: Provable, pos: SuccPos): Provable = {
      requireOneSubgoal(provable)
      provable(core.EquivifyRight(pos), 0)
    }
  }

  def HideL = new BuiltInLeftTactic("HideL") {
    override def applyAt(provable: Provable, pos: AntePos): Provable = {
      requireOneSubgoal(provable)
      provable(core.HideLeft(pos), 0)
    }
  }

  def HideR = new BuiltInRightTactic("HideR") {
    override def applyAt(provable: Provable, pos: SuccPos): Provable = {
      requireOneSubgoal(provable)
      provable(core.HideRight(pos), 0)
    }
  }

  def CoHideL = new BuiltInLeftTactic("CoHideL") {
    override def applyAt(provable: Provable, pos: AntePos): Provable = {
      requireOneSubgoal(provable)
      provable(core.CoHideLeft(pos), 0)
    }
  }

  def CoHideR = new BuiltInRightTactic("CoHideR") {
    override def applyAt(provable: Provable, pos: SuccPos): Provable = {
      requireOneSubgoal(provable)
      provable(core.CoHideRight(pos), 0)
    }
  }

  def CoHide2 = new BuiltInTwoPositionTactic("CoHide2") {
    override def applyAt(provable: Provable, posOne: Position, posTwo: Position): Provable = {
      requireOneSubgoal(provable)
      require(posOne.isAnte && posTwo.isSucc, "Should take an antecedent and a succedent position.")
      provable(core.CoHide2(posOne, posTwo), 0)
    }
  }

  def ExchangeL = new BuiltInTwoPositionTactic("ExchangeL") {
    override def applyAt(provable: Provable, posOne: Position, posTwo: Position): Provable = {
      requireOneSubgoal(provable)
      require(posOne.isAnte && posTwo.isAnte, "Both positions should be in the Antecedent.")
      provable(core.ExchangeLeftRule(posOne, posTwo), 0)
    }
  }

  def ExchangeR = new BuiltInTwoPositionTactic("ExchangeR") {
    override def applyAt(provable: Provable, posOne: Position, posTwo: Position): Provable = {
      requireOneSubgoal(provable)
      require(posOne.isSucc && posTwo.isSucc, "Both positions should be in the Succedent.")
      provable(core.ExchangeRightRule(posOne, posTwo), 0)
    }
  }

  def US(subst: USubst, origin: Sequent) = new BuiltInTactic("US") {
    override def result(provable: Provable): Provable = {
      requireOneSubgoal(provable)
      provable(core.UniformSubstitutionRule(subst, origin), 0)
    }
  }

  def Axiomatic(axiomName: String, subst: USubst) = new BuiltInTactic(s"US of Axiom $axiomName") {
    override def result(provable: Provable): Provable = {
      requireOneSubgoal(provable)
      provable(core.AxiomaticRule(axiomName, subst), 0)
    }
  }

  def UniformRenaming(what: Variable, repl: Variable) = new BuiltInTactic("UniformRenaming") {
    override def result(provable: Provable): Provable = {
      requireOneSubgoal(provable)
      provable(core.UniformRenaming(what, repl), 0)
    }
  }

  def BoundRenaming(what: Variable, repl: Variable) = new BuiltInTactic("BoundRenaming") {
    override def result(provable: Provable): Provable = {
      requireOneSubgoal(provable)
      provable(core.BoundRenaming(what, repl), 0)
    }
  }

  def Skolemize = new BuiltInPositionTactic("Skolemize") {
    override def applyAt(provable: Provable, pos: Position): Provable = {
      requireOneSubgoal(provable)
      provable(core.Skolemize(pos), 0)
    }
  }

  def DualFree = new BuiltInRightTactic("DualFree") {
    override def applyAt(provable: Provable, pos: SuccPos): Provable = {
      requireOneSubgoal(provable)
      provable(core.DualFree(pos), 0)
    }
  }

  /** Closes a goal with exactly the form \phi |- \phi; i.e., no surrounding context. */
  def TrivialCloser = new BuiltInTactic("CloseTrivialForm") {
    override def result(provable: Provable) = {
      requireOneSubgoal(provable)
      if(provable.subgoals.head.ante.length != 1 || provable.subgoals.head.succ.length != 1)
        throw BelleError(s"${this.name} should only be applied to formulas of the form \\phi |- \\phi")
      provable(core.Close(AntePos(0), SuccPos(0)), 0)
    }
  }

  /** Closes the goal using specified positions. */
  def Close = new BuiltInTwoPositionTactic("Close") {
    override def applyAt(provable: Provable, posOne: Position, posTwo: Position): Provable = {
      requireOneSubgoal(provable)
      require(posOne.isAnte && posTwo.isSucc, "Position one should be in the Antecedent, position two in the Succedent.")
      provable(core.Close(posOne, posTwo), 0)
    }
  }

  def CloseTrue = new BuiltInRightTactic("CloseTrue") {
    override def applyAt(provable: Provable, pos: SuccPos): Provable = {
      requireOneSubgoal(provable)
      provable(core.CloseTrue(pos), 0)
    }
  }

  def CloseFalse = new BuiltInLeftTactic("CloseFalse") {
    override def applyAt(provable: Provable, pos: AntePos): Provable = {
      requireOneSubgoal(provable)
      provable(core.CloseFalse(pos), 0)
    }
  }
}
