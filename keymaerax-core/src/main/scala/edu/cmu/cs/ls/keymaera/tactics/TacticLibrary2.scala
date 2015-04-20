package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.Formula

/**
 * Tactic library.
 * @author smitsch
 * Created by smitsch on 12/23/14.
 */
class TacticLibrary2(env : { val generator: Generator[Formula] }) {
  /**
   * Default tactics with invariant generation injected.
   */
  def default = BuiltinHigherTactics.master(env.generator, exhaustive = true, "Mathematica")
  def default(toolId : String) = BuiltinHigherTactics.master(env.generator, exhaustive = true, toolId)
  def defaultNoArith = BuiltinHigherTactics.noArith(env.generator, exhaustive = true)
}
