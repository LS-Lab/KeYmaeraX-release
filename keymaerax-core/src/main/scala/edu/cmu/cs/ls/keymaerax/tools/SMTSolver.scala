package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.core.{QETool, Term}

/**
 * Created by ran on 3/17/15.
 */
trait SMTSolver extends QETool {
  type KExpr = edu.cmu.cs.ls.keymaerax.core.Expression
  type SExpr = SMTLib

  def run(cmd : String) : (String, KExpr)

  /**
   * @return true if the job is finished, false if it is still running.
   */
  def ready : Boolean = ???

  /** Cancels the current request.
    * @return True if job is successfully cancelled, or False if the new
    * status is unknown.
    */
  def cancel : Boolean = ???


}