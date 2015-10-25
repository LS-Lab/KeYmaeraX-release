package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax
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

object Legacy {
  def Scheduled(tool: keymaerax.tools.Tool,
                tactic : keymaerax.tactics.Tactics.Tactic,
                timeout: Int = 0) = new BuiltInTactic(s"Scheduled(${tactic.name})") {
    override def result(provable: Provable): Provable = {
      //@todo don't know if we can create a proof node from a provable.
      if(provable.subgoals.length != 1) throw new Exception("Cannot run scheduled tactic on something with more than one subgoal.")
      val node = new keymaerax.tactics.RootNode(provable.subgoals.head)
      tactic(tool, node)

      //Note: completion events aren't used because they don't work... see the fact that some tactics
      //don't work in hte GUI.
      var waitTime = 0;
      while(!tactic.isComplete && (waitTime == 0 || waitTime > timeout)) {
        synchronized(wait(500));
        waitTime += 500
      };

      if(tactic.isComplete) node.provable
      else throw BelleError("Waited but the tactic still never finished.")
    }
  }
}
