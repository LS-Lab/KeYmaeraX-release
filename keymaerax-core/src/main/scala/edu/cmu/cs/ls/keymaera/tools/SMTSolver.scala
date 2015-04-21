package edu.cmu.cs.ls.keymaera.tools

import edu.cmu.cs.ls.keymaera.core.Term

/**
 * Created by ran on 3/17/15.
 */
trait SMTSolver extends QETool {
  type KExpr = edu.cmu.cs.ls.keymaera.core.Expression
  type SExpr = SMTLib

  val k2s = new KeYmaeraToSMT
  val s2k = new SMTToKeYmaera

  def toSMT(expr : KExpr): SExpr = k2s.convertToSMT(expr)
  def toKeYmaera(expr : String) : KExpr = s2k.convertToKeYmaera(expr)

  def run(cmd : String) : (String, KExpr)
//  def simplify(t : Term) : Term

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