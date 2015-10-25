package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
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
}

object Idioms {
  def NilT() = new BuiltInTactic("NilT") {
    override def result(provable: Provable): Provable = provable
  }
  def IdentT = NilT

  def AtSubgoal(subgoalIdx: Int, t: BelleExpr) = new DependentTactic(s"AtSubgoal($subgoalIdx, ${t.toString})") {
    override def computeExpr(v: BelleValue): BelleExpr = v match {
      case BelleProvable(provable) => {
        BranchTactic(Seq.tabulate(provable.subgoals.length)(i => if(i == subgoalIdx) t else IdentT))
      }
      case _ => throw BelleError("Cannot perform AtSubgoal on a non-Provable value.")
    }
  }
}
