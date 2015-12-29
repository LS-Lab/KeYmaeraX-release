package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.tactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.tactics.{Position, TacticWrapper, Interpreter, PosInExpr, Tactics}
import edu.cmu.cs.ls.keymaerax.tools.{KeYmaera, Mathematica}

import scala.language.postfixOps

/**
 * @author Nathan Fulton
 */
object DebuggingTactics {
  //@todo import a debug flag as in Tactics.DEBUG
  private val DEBUG = System.getProperty("DEBUG", "false")=="true"

  def error(e : Throwable) = new BuiltInTactic("Error") {
    override def result(provable: Provable): Provable = throw e
  }

  def error(s: => String) = new BuiltInTactic("Error") {
    override def result(provable: Provable): Provable = {
      throw new BelleUserGeneratedError(s)
    }
  }

  /** debug is a no-op tactic that prints a message and the current provable, if the system property DEBUG is true. */
  def debug(message: => String): BuiltInTactic = new BuiltInTactic("debug") {
    override def result(provable: Provable): Provable = {
      if (DEBUG) println("===== " + message + " ==== " + provable + " =====")
      provable
    }
  }

  /** debug is a no-op tactic that prints a message and the current provable, if the system property DEBUG is true. */
  def debugAt(message: => String): BuiltInPositionTactic = new BuiltInPositionTactic("debug") {
    override def computeResult(provable: Provable, pos: Position): Provable = {
      if (DEBUG) println("===== " + message + " ==== " + "\n\t with formula: " + provable.subgoals.head.at(pos)
        + " at position " + pos + " of first subgoal,"
        + "\n\t entire provable: " + provable + " =====")
      provable
    }
  }

  /** assert is a no-op tactic that raises an error if the provable is not of the expected size. */
  def assert(anteSize: Int, succSize: Int, msg: => String = ""): BuiltInTactic = new BuiltInTactic("assert") {
    override def result(provable: Provable): Provable = {
      if (provable.subgoals.size != 1 || provable.subgoals.head.ante.size != anteSize ||
        provable.subgoals.head.succ.size != succSize) {
        throw new BelleUserGeneratedError(msg + "\nExpected 1 subgoal with: " + anteSize + " antecedent and " + succSize + " succedent formulas,\n\t but got " +
          provable.subgoals.size + " subgoals (head subgoal with: " + provable.subgoals.head.ante.size + "antecedent and " +
          provable.subgoals.head.succ.size + " succedent formulas)")
      }
      provable
    }
  }

  /** assert is a no-op tactic that raises an error if the provable has not the expected formula at the specified position. */
  def assert(fml: Formula, message: => String): BuiltInPositionTactic = new BuiltInPositionTactic("assert") {
    override def computeResult(provable: Provable, pos: Position): Provable = {
      if (provable.subgoals.size != 1 || provable.subgoals.head.at(pos)._2 != fml) {
        throw new BelleUserGeneratedError(message + "\nExpected 1 subgoal with " + fml + " at position " + pos + ",\n\t but got " +
          provable.subgoals.size + " subgoals (head subgoal with " + provable.subgoals.head.at(pos) + " at position " + pos + ")")
      }
      provable
    }
  }

  /** assert is a no-op tactic that raises an error if the provable does not satisfy a condition. */
  def assert(cond: Sequent=>Boolean, message: => String): BuiltInTactic = new BuiltInTactic("assert") {
    override def result(provable: Provable): Provable = {
      if (provable.subgoals.size != 1 || !cond(provable.subgoals.head)) {
        throw new BelleUserGeneratedError(message + "\nExpected 1 subgoal whose sequent matches condition " + cond + ",\n\t but got " +
          provable.subgoals.size + " subgoals, or sole subgoal does not match")
      }
      provable
    }
  }

  /** assert is a no-op tactic that raises an error if the provable does not satisfy a condition at position pos. */
  def assert(cond: (Sequent,Position)=>Boolean, message: => String): BuiltInPositionTactic = new BuiltInPositionTactic("assert") {
    override def computeResult(provable: Provable, pos: Position): Provable = {
      if (provable.subgoals.size != 1 || !cond(provable.subgoals.head, pos)) {
        throw new BelleUserGeneratedError(message + "\nExpected 1 subgoal whose sequent matches condition " + cond + " at position " + pos + ",\n\t but got " +
          provable.subgoals.size + " subgoals, or sole subgoal formula " + provable.subgoals.head.at(pos) + " does not match")
      }
      provable
    }
  }

  /** assertE is a no-op tactic that raises an error if the provable has not the expected expression at the specified position. */
  def assertE(expected: => Expression, message: => String): BuiltInPositionTactic = new BuiltInPositionTactic("assert") {
    override def computeResult(provable: Provable, pos: Position): Provable = {
      if (provable.subgoals.size != 1 || provable.subgoals.head.at(pos)._2 != expected) {
        throw new BelleUserGeneratedError(message + "\nExpected 1 subgoal with " + expected + " at position " + pos + ",\n\t but got " +
          provable.subgoals.size + " subgoals (head subgoal with " + provable.subgoals.head.at(pos) + " at position " + pos + ")")
      }
      provable
    }
  }

  /** no-op tactic that raises an error if the provable is not proved */
  lazy val assertProved = new BuiltInTactic("assert proved") {
    override def result(provable : Provable): Provable =
      if (provable.isProved) provable
      else throw new BelleError("Expected proved provable, but got " + provable)
  }
}

/**
 * @author Nathan Fulton
 */
object Idioms {
  lazy val nil = PartialTactic(new BuiltInTactic("NilT") {
    override def result(provable: Provable): Provable = provable
  })
  lazy val ident = nil

  /** Optional tactic */
  def ?(t: BelleExpr): BelleExpr = (t partial) | nil

  /** Mandatory change */
  def must(t: BelleExpr): BelleExpr = new DependentTactic("must") {
    override def computeExpr(before: Provable): BelleExpr = t & new BuiltInTactic(name) {
      override def result(after: Provable): Provable = {
        if (before == after) throw new BelleError("Tactic " + t + " did not result in mandatory change")
        after
      }
    }
  }

  def atSubgoal(subgoalIdx: Int, t: BelleExpr) = new DependentTactic(s"AtSubgoal($subgoalIdx, ${t.toString})") {
    override def computeExpr(v: BelleValue): BelleExpr = v match {
      case BelleProvable(provable) =>
        BranchTactic(Seq.tabulate(provable.subgoals.length)(i => if(i == subgoalIdx) t else ident))
      case _ => throw new BelleError("Cannot perform AtSubgoal on a non-Provable value.")
    }
  }

  /** Gives a name to a tactic to a definable tactic. */
  def NamedTactic(name: String, tactic: BelleExpr) = new DependentTactic(name) {
    override def computeExpr(v: BelleValue): BelleExpr = tactic
  }

  /** Establishes the fact by appealing to an existing tactic. */
  def by(fact: Provable) = new BuiltInTactic("Established by existing provable") {
    override def result(provable: Provable): Provable = {
      assert(provable.subgoals.length == 1, "Expected one subgoal but found " + provable.subgoals.length)
      provable(fact, 0)
    }
  }

  /**
   * shift(shift, t) does t shifted from position p to shift(p)
   */
  def shift(shift: PosInExpr=>PosInExpr, t: DependentPositionTactic): DependentPositionTactic =
    new DependentPositionTactic("Shift " + t) {
      override def factory(pos: Position): DependentTactic = t.apply(pos.navigate(shift(pos.inExpr)))
    }
  /**
   * shift(child, t) does t to positions shifted by child
   */
  def shift(child: PosInExpr, t: DependentPositionTactic): DependentPositionTactic = shift(p => p.append(child), t)
}

/** Creates tactic objects */
object TacticFactory {

  /**
   * Creates named dependent tactics.
   * @example{{{
   *  "[:=] assign" by (pos => useAt("[:=] assign")(pos))
   * }}}
   * @param name The tactic name.
   */
  implicit class TacticForNameFactory(val name: String) {
    /** Creates a dependent position tactic without inspecting the formula at that position */
    def by(t: (Position => BelleExpr)): DependentPositionTactic = new DependentPositionTactic(name) {
      override def factory(pos: Position): DependentTactic = new DependentTactic(name) {
        override def computeExpr(provable: Provable): BelleExpr = t(pos)
      }
    }

    /** Creates a dependent position tactic while inspecting the formula at that position */
    def by(t: ((Position, Sequent) => BelleExpr)): DependentPositionTactic = new DependentPositionTactic(name) {
      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = t(pos, sequent)
      }
    }
  }

}

/**
 * @author Nathan Fulton
 */
object Legacy {
  /** The default mechanism for initializing KeYmaeraScheduler, Mathematica, and Z3 that are used in the legacy tactics.
    * @note This may interfere in unexpected ways with sequential tactics.
    */
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

  def initializedScheduledTactic(mathematicaConfig : Map[String,String], tactic: keymaerax.tactics.Tactics.Tactic) = {
    defaultInitialization(mathematicaConfig)
    scheduledTactic(tactic)
  }

  def scheduledTactic(tactic : keymaerax.tactics.Tactics.Tactic) = new BuiltInTactic(s"Scheduled(${tactic.name})") {
    //@see [[Legacy.defaultInitialization]]
    if(!Tactics.KeYmaeraScheduler.isInitialized)
      throw new BelleError("Need to initialize KeYmaera scheduler and possibly also the Mathematica scheduler before running a Legacy.ScheduledTactic.")

    override def result(provable: Provable): Provable = {
      //@todo don't know if we can create a proof node from a provable.
      if(provable.subgoals.length != 1) throw new Exception("Cannot run scheduled tactic on something with more than one subgoal.")

      val node = new keymaerax.tactics.RootNode(provable.subgoals.head)

      Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, node))

      node.provableWitness
    }
  }
}