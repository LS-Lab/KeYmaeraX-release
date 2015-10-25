package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleUserGeneratedError, BuiltInTactic}
import edu.cmu.cs.ls.keymaerax.core.Provable

/**
 * @author Nathan Fulton
 */
object DebuggingTactics {
  def ErrorT(e : Throwable) = new BuiltInTactic("Error") {
    override def result(provable: Provable): Provable = throw e
  }

  def ErrorT(s : String) = new BuiltInTactic("Error") {
    override def result(provable: Provable): Provable = {
      throw BelleUserGeneratedError(s)
    }
  }

  def NilT() = new BuiltInTactic("NilT") {
    override def result(provable: Provable): Provable = provable
  }
  def Ident = NilT
}
