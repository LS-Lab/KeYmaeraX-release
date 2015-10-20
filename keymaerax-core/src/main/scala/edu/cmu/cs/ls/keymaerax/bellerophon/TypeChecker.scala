package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.UnificationMatch

/**
 * The type checker for Bellerophon.
 * @author Nathan Fulton
 */
object TypeChecker {
  /**
   * @todo unimplemented.
   */
  def apply(e: BelleExpr, t: BelleType) = true


  /**
   * Unification matching to find a uniform substitution s.t. usubst(on) = matching
   * @note This method is used by both the TypeChecker and the Interpreter.
   * @return a uniform substitution such that \result(on) = matching, if exists.
   */
  def findSubst(on: BelleType, matching: Seq[Provable]): Option[USubst] = on match {
    case BelleTypeVariable(n) => ??? /*
    @todo like this except return the actual match as opposed to just reporting existence.
    @todo also richer core data needed to match more interesting shapes
    matching.find(proof => proof.subgoals.find(s => s.succ.find(
      f => UnificationMatch.unifiable(PredOf(Function(n,None,Unit,Bool),Nothing), f).isDefined)))*/
  }
}
