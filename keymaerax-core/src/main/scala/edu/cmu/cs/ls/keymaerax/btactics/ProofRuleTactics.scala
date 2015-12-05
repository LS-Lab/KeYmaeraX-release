package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.{SuccPosition, AntePosition, Position}


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

  def applyRule(rule: Rule): BuiltInTactic = new BuiltInTactic("Apply Rule") {
    override def result(provable: Provable): Provable = {
      requireOneSubgoal(provable)
      provable(rule, 0)
    }
  }

  def cut(f: Formula) = new InputTactic[Formula](f) {
    override def computeExpr() = new BuiltInTactic(s"Cut(${input.prettyString})") {
      override def result(provable: Provable): Provable = {
        provable(core.Cut(input), 0)
      }
    }
  }

  def cutL(f: Formula)(pos: AntePos) = new InputTactic[Formula](f) {
    override def computeExpr() = new BuiltInTactic("CutL") {
      override def result(provable: Provable): Provable = {
        requireOneSubgoal(provable)
        provable(core.CutLeft(f, pos), 0)
      }
    }
  }

  def cutR(f: Formula)(pos: SuccPos) = new InputTactic[Formula](f) {
    override def computeExpr() = new BuiltInTactic("CutR") {
      override def result(provable: Provable): Provable = {
        requireOneSubgoal(provable)
        provable(core.CutRight(f, pos), 0)
      }
    }
  }

  def cutLR(f: Formula)(pos: Position) = new InputTactic[Formula](f) {
    override def computeExpr() = new BuiltInTactic("CutLR") {
      override def result(provable: Provable): Provable = {
        requireOneSubgoal(provable)
        if (pos.isAnte) provable(core.CutLeft(f, pos), 0)
        else provable(core.CutRight(f, pos), 0)
      }
    }
  }

  def notL = new BuiltInLeftTactic("NotL") {
    override def computeAnteResult(provable: Provable, pos: AntePosition): Provable = {
      requireOneSubgoal(provable)
      provable(core.NotLeft(pos), 0)
    }
  }

  def notR = new BuiltInRightTactic("NotR") {
    override def computeSuccResult(provable: Provable, pos: SuccPosition): Provable = {
      requireOneSubgoal(provable)
      provable(core.NotRight(pos), 0)
    }
  }

  def andR = new BuiltInRightTactic("AndR") {
    override def computeSuccResult(provable: Provable, pos : SuccPosition) = {
      requireOneSubgoal(provable)
      provable(core.AndRight(pos), 0)
    }
  }

  def andL = new BuiltInLeftTactic("AndL") {
    override def computeAnteResult(provable: Provable, pos: AntePosition) = {
      requireOneSubgoal(provable)
      provable(core.AndLeft(pos), 0)
    }
  }

  def orR = new BuiltInRightTactic("OrR") {
    override def computeSuccResult(provable: Provable, pos : SuccPosition) = {
      requireOneSubgoal(provable)
      provable(core.OrRight(pos), 0)
    }
  }

  def orL = new BuiltInLeftTactic("OrL") {
    override def computeAnteResult(provable: Provable, pos: AntePosition) = {
      requireOneSubgoal(provable)
      provable(core.OrLeft(pos), 0)
    }
  }

  def implyR = new BuiltInRightTactic("ImplyR") {
    override def computeSuccResult(provable : Provable, pos : SuccPosition) = {
      requireOneSubgoal(provable)
      provable(core.ImplyRight(pos), 0)
    }
  }

  def implyL = new BuiltInLeftTactic("ImplyL") {
    override def computeAnteResult(provable : Provable, pos: AntePosition) = {
      requireOneSubgoal(provable)
      provable(core.ImplyLeft(pos), 0)
    }
  }

  def equivR = new BuiltInRightTactic("EquivR") {
    override def computeSuccResult(provable: Provable, pos: SuccPosition): Provable = {
      requireOneSubgoal(provable)
      provable(core.EquivRight(pos), 0)
    }
  }

  def equivL = new BuiltInLeftTactic("EquivL") {
    override def computeAnteResult(provable: Provable, pos: AntePosition): Provable = {
      requireOneSubgoal(provable)
      provable(core.EquivLeft(pos), 0)
    }
  }

  def commuteEquivL = new BuiltInLeftTactic("CommuteEquivL") {
    override def computeAnteResult(provable: Provable, pos: AntePosition): Provable = {
      requireOneSubgoal(provable)
      provable(core.CommuteEquivLeft(pos), 0)
    }
  }

  def commuteEquivR = new BuiltInRightTactic("CommuteEquivR") {
    override def computeSuccResult(provable: Provable, pos: SuccPosition): Provable = {
      requireOneSubgoal(provable)
      provable(core.CommuteEquivRight(pos), 0)
    }
  }

  def equivifyR = new BuiltInRightTactic("EquivifyR") {
    override def computeSuccResult(provable: Provable, pos: SuccPosition): Provable = {
      requireOneSubgoal(provable)
      provable(core.EquivifyRight(pos), 0)
    }
  }

  def hide = new DependentPositionTactic("Hide") {
    override def apply(pos: Position): DependentTactic = pos match {
      case p: AntePosition => new DependentTactic(name) {
        override def computeExpr(v: BelleValue): BelleExpr = hideL(p)
      }
      case p: SuccPosition => new DependentTactic(name) {
        override def computeExpr(v: BelleValue): BelleExpr = hideR(p)
      }
    }
  }

  def hideL = new BuiltInLeftTactic("HideL") {
    override def computeAnteResult(provable: Provable, pos: AntePosition): Provable = {
      requireOneSubgoal(provable)
      provable(core.HideLeft(pos), 0)
    }
  }

  def hideR = new BuiltInRightTactic("HideR") {
    override def computeSuccResult(provable: Provable, pos: SuccPosition): Provable = {
      requireOneSubgoal(provable)
      provable(core.HideRight(pos), 0)
    }
  }

  def coHide = new DependentPositionTactic("CoHide") {
    override def apply(pos: Position): DependentTactic = pos match {
      case p: AntePosition => new DependentTactic(name) {
        override def computeExpr(v: BelleValue): BelleExpr = coHideL(p)
      }
      case p: SuccPosition => new DependentTactic(name) {
        override def computeExpr(v: BelleValue): BelleExpr = coHideR(p)
      }
    }
  }

  def coHideL = new BuiltInLeftTactic("CoHideL") {
    override def computeAnteResult(provable: Provable, pos: AntePosition): Provable = {
      requireOneSubgoal(provable)
      provable(core.CoHideLeft(pos), 0)
    }
  }

  def coHideR = new BuiltInRightTactic("CoHideR") {
    override def computeSuccResult(provable: Provable, pos: SuccPosition): Provable = {
      requireOneSubgoal(provable)
      provable(core.CoHideRight(pos), 0)
    }
  }

  def coHide2 = new BuiltInTwoPositionTactic("CoHide2") {
    override def computeResult(provable: Provable, posOne: Position, posTwo: Position): Provable = {
      requireOneSubgoal(provable)
      require(posOne.isAnte && posTwo.isSucc, "Should take an antecedent and a succedent position.")
      provable(core.CoHide2(posOne, posTwo), 0)
    }
  }

  def exchangeL = new BuiltInTwoPositionTactic("ExchangeL") {
    override def computeResult(provable: Provable, posOne: Position, posTwo: Position): Provable = {
      requireOneSubgoal(provable)
      require(posOne.isAnte && posTwo.isAnte, "Both positions should be in the Antecedent.")
      provable(core.ExchangeLeftRule(posOne, posTwo), 0)
    }
  }

  def exchangeR = new BuiltInTwoPositionTactic("ExchangeR") {
    override def computeResult(provable: Provable, posOne: Position, posTwo: Position): Provable = {
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

  def axiomatic(axiomName: String, subst: USubst) = new BuiltInTactic(s"US of Axiom $axiomName") {
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
    override def computeResult(provable: Provable, pos: Position): Provable = {
      requireOneSubgoal(provable)
      provable(core.Skolemize(pos), 0)
    }
  }

  def skolemizeR = new BuiltInRightTactic("Skolemize") {
    override def computeSuccResult(provable: Provable, pos: SuccPosition): Provable = {
      requireOneSubgoal(provable)
      provable(core.Skolemize(pos), 0)
    }
  }

  def skolemizeL = new BuiltInLeftTactic("Skolemize") {
    override def computeAnteResult(provable: Provable, pos: AntePosition): Provable = {
      requireOneSubgoal(provable)
      provable(core.Skolemize(pos), 0)
    }
  }

  def dualFree = new BuiltInRightTactic("DualFree") {
    override def computeSuccResult(provable: Provable, pos: SuccPosition): Provable = {
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
    override def computeResult(provable: Provable, posOne: Position, posTwo: Position): Provable = {
      requireOneSubgoal(provable)
      require(posOne.isAnte && posTwo.isSucc, "Position one should be in the Antecedent, position two in the Succedent.")
      provable(core.Close(posOne, posTwo), 0)
    }
  }

  def closeTrue = new BuiltInRightTactic("CloseTrue") {
    override def computeSuccResult(provable: Provable, pos: SuccPosition): Provable = {
      requireOneSubgoal(provable)
      provable(core.CloseTrue(pos), 0)
    }
  }

  def closeFalse = new BuiltInLeftTactic("CloseFalse") {
    override def computeAnteResult(provable: Provable, pos: AntePosition): Provable = {
      requireOneSubgoal(provable)
      provable(core.CloseFalse(pos), 0)
    }
  }
}
