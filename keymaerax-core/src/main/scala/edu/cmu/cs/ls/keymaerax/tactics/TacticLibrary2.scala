/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core.Formula

/**
 * Tactic library.
 * @author smitsch
 * Created by smitsch on 12/23/14.
 */
@deprecated("Use TactixLibrary instead.")
class TacticLibrary2(env : { val generator: Generator[Formula] }) {
  /**
   * Default tactics with invariant generation injected.
   */
  def default = BuiltinHigherTactics.master(env.generator, exhaustive = true, "Mathematica")
  def default(toolId : String) = BuiltinHigherTactics.master(env.generator, exhaustive = true, toolId)
  def defaultNoArith = BuiltinHigherTactics.noArith(env.generator, exhaustive = true)
}
