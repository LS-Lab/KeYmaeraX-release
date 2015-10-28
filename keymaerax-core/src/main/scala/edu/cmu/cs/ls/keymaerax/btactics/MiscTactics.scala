package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core.Provable
import edu.cmu.cs.ls.keymaerax.tactics.{TacticWrapper, Interpreter, Tactics, ProofNode}
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaera, Mathematica}

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
  def defaultInitialization(mathematicaConfig:  Map[String,String]) = {
    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)

    Tactics.KeYmaeraScheduler.init(Map())
    Tactics.Z3Scheduler.init
    Tactics.MathematicaScheduler.init(mathematicaConfig)
  }

//  def defaultDeinitialization = {
//    if (Tactics.KeYmaeraScheduler != null) {
//      Tactics.KeYmaeraScheduler.shutdown()
//      Tactics.KeYmaeraScheduler = null
//    }
//    if (Tactics.MathematicaScheduler != null) {
//      Tactics.MathematicaScheduler.shutdown()
//      Tactics.MathematicaScheduler = null
//    }
//    if(Tactics.Z3Scheduler != null) {
//      Tactics.Z3Scheduler = null
//    }
//  }

  def InitializedScheduledTactic(mathematicaConfig : Map[String,String], tactic: keymaerax.tactics.Tactics.Tactic) = {
    defaultInitialization(mathematicaConfig)
    ScheduledTactic(tactic)
  }

  def ScheduledTactic(tactic : keymaerax.tactics.Tactics.Tactic) = new BuiltInTactic(s"Scheduled(${tactic.name})") {
    //@see [[Legacy.defaultInitialization]]
    if(!Tactics.KeYmaeraScheduler.isInitialized)
      throw BelleError("Need to initialize KeYmaera scheduler and possibly also the Mathematica scheduler before running a Legacy.ScheduledTactic.")

    override def result(provable: Provable): Provable = {
      //@todo don't know if we can create a proof node from a provable.
      if(provable.subgoals.length != 1) throw new Exception("Cannot run scheduled tactic on something with more than one subgoal.")

      val node = new keymaerax.tactics.RootNode(provable.subgoals.head)

      Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, node))

      node.provableWitness
    }
  }
}
