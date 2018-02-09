/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.core

/**
  * Continuous invariant generation tool.
  * @see [[edu.cmu.cs.ls.keymaerax.btactics.ToolProvider]]
  */
trait InvGenTool {
  /**
    * Returns a continuous invariant for a safety problem sent to the tool.
    * @params (precondition, ode, postcondition) Hoare triple for safety verification.
    * @return a continuous invariant.
    */
  def invgen(problem:String): Formula
}

