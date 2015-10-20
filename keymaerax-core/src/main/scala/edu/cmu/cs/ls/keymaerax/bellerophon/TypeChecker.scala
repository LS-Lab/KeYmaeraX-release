package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.{USubst, Provable}

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
   * Attempts to find a uniform substitution s.t. usubst(on) = matching
   * @note This method is used by both the TypeChecker and the Interpreter.
   * @return
   */
  def findSubst(on: BelleType, matching: Seq[Provable]): Option[USubst] = ???
}
