package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core._
import Augmentors._
import ProofRuleTactics.requireOneSubgoal
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

import scala.language.postfixOps

/**
 * @author Nathan Fulton
 */
object DebuggingTactics {
  //@todo import a debug flag as in Tactics.DEBUG
  private val DEBUG = System.getProperty("DEBUG", "false")=="true"

  def error(e : Throwable) = new BuiltInTactic("Error") {
    override def result(provable: ProvableSig): ProvableSig = throw e
  }

  def error(s: => String) = new BuiltInTactic("Error") {
    override def result(provable: ProvableSig): ProvableSig = {
      throw new BelleUserGeneratedError(s)
    }
  }

  def recordQECall(): BuiltInTactic = new BuiltInTactic("recordQECall") {
    override def result(provable: ProvableSig): ProvableSig = {
      println(s"QE CALL\n==QE==\n${provable.subgoals(0).prettyString}\n==END_QE==")
      provable
    }
  }

  /** debug is a no-op tactic that prints a message and the current provable, if doPrint (defaults to the system property DEBUG) is true. */
  def debug(message: => String, doPrint: Boolean = DEBUG, printer: ProvableSig => String = _.toString): BuiltInTactic =
      new BuiltInTactic("debug") {
    override def result(provable: ProvableSig): ProvableSig = {
      if (doPrint) println("===== " + message + " ==== " + printer(provable) + " =====")
      provable
    }
  }

  /** print is a no-op tactic that prints a message and the current provable, regardless of DEBUG being true or false */
  def print(message: => String): BuiltInTactic = debug(message, doPrint=true)
  /** printIndexed is a no-op tactic that prints a message and the current provable (verbose sequent with formula indices),
    * regardless of DEBUG being true or false */
  def printIndexed(message: => String): BuiltInTactic = debug(message, doPrint=true, _.prettyString)

  /** debug is a no-op tactic that prints a message and the current provable, if the system property DEBUG is true. */
  def debugAt(message: => String, doPrint: Boolean = DEBUG): BuiltInPositionTactic = new BuiltInPositionTactic("debug") {
    override def computeResult(provable: ProvableSig, pos: Position): ProvableSig = {
      if (doPrint) println("===== " + message + " ==== " + "\n\t with formula: " + provable.subgoals.head.at(pos)
        + " at position " + pos + " of first subgoal,"
        + "\n\t entire provable: " + provable + " =====")
      provable
    }
  }

  /**
    * Assert that the assertion holds at a the specified position. Could be a non-top-level position. Analogous to [[debugAt]].
    * @param msg The message to display.
    * @param assertion The assertion.
    */
  def assertAt(msg: Expression => String, assertion: Expression => Boolean): BuiltInPositionTactic = new BuiltInPositionTactic("NOT_EXTRACTABLE") {
    override def computeResult(provable: ProvableSig, pos: Position): ProvableSig = {
      val ctx = provable.subgoals.head.at(pos)
      if (!assertion(ctx._2))
        throw new BelleUserGeneratedError("Assertion Failed: " + msg(ctx._2) + "\nAt:\n" + ctx)
      provable
    }
  }

  def assertAt(msg: => String, assertion: Expression => Boolean): BuiltInPositionTactic = assertAt((e:Expression) => msg, assertion)

  /** assert is a no-op tactic that raises an error if the provable is not of the expected size. */
  def assert(anteSize: Int, succSize: Int, msg: => String = ""): BuiltInTactic = new BuiltInTactic("assert") {
    override def result(provable: ProvableSig): ProvableSig = {
      if (provable.subgoals.size != 1 || provable.subgoals.head.ante.size != anteSize ||
        provable.subgoals.head.succ.size != succSize) {
        throw new BelleUserGeneratedError(msg + "\nExpected 1 subgoal with: " + anteSize + " antecedent and " + succSize + " succedent formulas,\n\t but got " +
          provable.subgoals.size + " subgoals (head subgoal with: " + provable.subgoals.head.ante.size + "antecedent and " +
          provable.subgoals.head.succ.size + " succedent formulas)")
      }
      provable
    }
  }

  //@todo rename to something else otherwise scala assert no longer works!
  /** assert is a no-op tactic that raises an error if the provable has not the expected formula at the specified position. */
  def assert(fml: Formula, message: => String): BuiltInPositionTactic = new BuiltInPositionTactic("assert") {
    override def computeResult(provable: ProvableSig, pos: Position): ProvableSig = {
      if (provable.subgoals.size != 1 || provable.subgoals.head.at(pos)._2 != fml) {
        throw new BelleUserGeneratedError(message + "\nExpected 1 subgoal with " + fml + " at position " + pos + ",\n\t but got " +
          provable.subgoals.size + " subgoals (head subgoal with " + provable.subgoals.head.sub(pos) + " at position " + pos + ")")
      }
      provable
    }
  }

  /** assert is a no-op tactic that raises an error if the provable does not satisfy a condition. */
  def assert(cond: Sequent=>Boolean, message: => String): BuiltInTactic = new BuiltInTactic("assert") {
    override def result(provable: ProvableSig): ProvableSig = {
      if (provable.subgoals.size != 1 || !cond(provable.subgoals.head)) {
        throw new BelleUserGeneratedError(message + "\nExpected 1 subgoal whose sequent matches condition " + cond + ",\n\t but got " +
          provable.subgoals.size + " subgoals, or sole subgoal does not match")
      }
      provable
    }
  }

  def assertProvableSize(provableSize: Int): BuiltInTactic = new BuiltInTactic(s"assertProvableSize(${provableSize})") {
    override def result(provable: ProvableSig): ProvableSig = {
      if (provable.subgoals.length != provableSize)
        throw new BelleUserGeneratedError(s"assertProvableSize failed: Expected to have ${provableSize} open goals but found an open goal with ${provable.subgoals.size}");
      provable
    }
  }

  /** assert is a no-op tactic that raises an error if the provable does not satisfy a condition at position pos. */
  def assert(cond: (Sequent,Position)=>Boolean, message: => String): BuiltInPositionTactic = new BuiltInPositionTactic("assert") {
    override def computeResult(provable: ProvableSig, pos: Position): ProvableSig = {
      if (provable.subgoals.size != 1 || !cond(provable.subgoals.head, pos)) {
        throw new BelleUserGeneratedError(message + "\nExpected 1 subgoal whose sequent matches condition " + cond + " at position " + pos + ",\n\t but got " +
          provable.subgoals.size + " subgoals, or sole subgoal formula " + provable.subgoals.head.at(pos) + " does not match")
      }
      provable
    }
  }

  /** assertE is a no-op tactic that raises an error if the provable has not the expected expression at the specified position. */
  def assertE(expected: => Expression, message: => String): BuiltInPositionTactic = new BuiltInPositionTactic("assert") {
    override def computeResult(provable: ProvableSig, pos: Position): ProvableSig = {
      if (provable.subgoals.size != 1 || provable.subgoals.head.at(pos)._2 != expected) {
        throw new BelleUserGeneratedError(message + "\nExpected 1 subgoal with " + expected + " at position " + pos + ",\n\t but got " +
          provable.subgoals.size + " subgoals (head subgoal with " + provable.subgoals.head.at(pos) + " at position " + pos + ")")
      }
      provable
    }
  }

  /** @see [[TactixLibrary.done]] */
  lazy val done: BelleExpr = done()
  def done(msg: String = ""): BelleExpr = new BuiltInTactic("done") {
    override def result(provable : ProvableSig): ProvableSig =
      if (provable.isProved) provable
      else throw new BelleThrowable((if (msg.nonEmpty) msg+"\n" else "") + "Expected proved provable, but got " + provable)
  }
}

case class Case(fml: Formula, simplify: Boolean = true) {
  def prettyString: String = s"Case '${fml.prettyString}'"
}

/**
 * @author Nathan Fulton
 */
object Idioms {
  import TacticFactory._

  lazy val nil: BelleExpr = new BuiltInTactic("nil") {
    override def result(provable: ProvableSig): ProvableSig = provable
  }
  lazy val ident: BelleExpr = nil

  /** Optional tactic */
  def ?(t: BelleExpr): BelleExpr = (t partial) | nil

  /** Execute ts by branch order. */
  def <(t: BelleExpr*): BelleExpr = BranchTactic(t)

  /** Execute ts by branch label, fall back to branch order if branches come without labels.
    * <((lbl1,t1), (lbl2,t2)) uses tactic t1 on branch labelled lbl1 and t2 on lbl2
    */
  def <(s1: (BelleLabel, BelleExpr), spec: (BelleLabel, BelleExpr)*): BelleExpr = new LabelledGoalsDependentTactic("onBranch") {
    override def computeExpr(provable: ProvableSig, labels: List[BelleLabel]): BelleExpr = {
      val labelledTactics = (s1 +: spec).toMap
      Idioms.<(labels.map(l => labelledTactics(l)):_*)
    }
    override def computeExpr(provable: ProvableSig): BelleExpr = {
      if (DEBUG) println("No branch labels, executing by branch order")
      Idioms.<((s1 +: spec).map(_._2):_*)
    }
  }

  /* branch by case distinction
  *  cases must be exhaustive (or easily proved to be exhaustive in context)
  *  otherwise, the exhaustiveness case is left open
  * */
  def cases(exhaustive: BelleExpr = TactixLibrary.master())(c1: (Case, BelleExpr), cs: (Case, BelleExpr)*): BelleExpr = {
    val cases = c1 +: cs
    val caseFml = cases.map({ case (Case(fml, _), _) => fml }).reduceRight(Or)

    //@todo simplify with only the case formula as simplification 'context' (adapt simplifier)
    val simplify = (fml: Formula) => SimplifierV2.simpTac//(Some(scala.collection.immutable.IndexedSeq(fml)))
    val simplifyAllButCase = (fml: Formula) => "ANON" by {(seq: Sequent) =>
      (0 until seq.ante.length-1).map(i => simplify(fml)(AntePosition.base0(i))).reduceOption[BelleExpr](_&_).getOrElse(ident) &
      seq.succ.indices.map(i => simplify(fml)(SuccPosition.base0(i))).reduceOption[BelleExpr](_&_).getOrElse(ident)
    }

    val caseTactics = cases.map({ case (Case(fml, doSimp), t) =>
      (if (doSimp) simplifyAllButCase(fml) & ((TactixLibrary.hideL('L, True) | TactixLibrary.hideR('R, False))*) else ident) & t}).
      reduceRight[BelleExpr]({ case (t1, t2) => TactixLibrary.orL('Llast) & Idioms.<(t1, t2)})

    TactixLibrary.cut(caseFml) & Idioms.<(
      /*use*/ caseTactics,
      // cases might be exhaustive in itself (e.g., x>=0|x<0), or exhaustive per facts from antecedent (x=0|x>0 from x>=0)
      /*show*/
        TactixLibrary.cohideR('Rlast) & exhaustive & TactixLibrary.done |
        TactixLibrary.cohideOnlyR('Rlast) & exhaustive & TactixLibrary.done | exhaustive & TactixLibrary.done | ident
    )
  }
  def cases(c1: (Case, BelleExpr), cs: (Case, BelleExpr)*): BelleExpr = cases()(c1, cs:_*)

  /** Repeats t while condition at position is true. */
  def repeatWhile(condition: Expression => Boolean)(t: BelleExpr): DependentPositionTactic = "loopwhile" by {(pos: Position) =>
    (DebuggingTactics.assertAt((_: Expression) => "Stopping loop", condition)(pos) & t)*
  }

  /** must(t) runs tactic `t` but only if `t` actually changed the goal. */
  def must(t: BelleExpr): BelleExpr = new DependentTactic("must") {
    override def computeExpr(before: ProvableSig): BelleExpr = t & new BuiltInTactic(name) {
      override def result(after: ProvableSig): ProvableSig = {
        if (before == after) throw new BelleThrowable("Tactic " + t + " did not result in mandatory change")
        after
      }
    }
  }

  def atSubgoal(subgoalIdx: Int, t: BelleExpr) = new DependentTactic(s"AtSubgoal($subgoalIdx, ${t.toString})") {
    override def computeExpr(v: BelleValue): BelleExpr = v match {
      case BelleProvable(provable, _) =>
        BranchTactic(Seq.tabulate(provable.subgoals.length)(i => if(i == subgoalIdx) t else ident))
      case _ => throw new BelleThrowable("Cannot perform AtSubgoal on a non-Provable value.")
    }
  }

  /** Gives a name to a tactic to a definable tactic. */
  def NamedTactic(name: String, tactic: BelleExpr) = new DependentTactic(name) {
    override def computeExpr(v: BelleValue): BelleExpr = tactic
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
  def shift(child: PosInExpr, t: DependentPositionTactic): DependentPositionTactic = shift(p => p ++ child, t)
}

/** Creates tactic objects */
object TacticFactory {

  /**
   * Creates named dependent tactics.
   * @example{{{
   *  "[:=] assign" by (pos => useAt("[:=] assign")(pos))
   * }}}
   * @param name The tactic name.
    *             Use the special name "ANON" to indicate that this is an anonymous inner tactic that needs no storage.
   */
  implicit class TacticForNameFactory(val name: String) {
    if (name == "") throw new InternalError("Don't use empty name, use ANON for anonymous inner tactics")
    /*if (false)*/ {
      try {
        if (name != "ANON" && DerivationInfo.ofCodeName(name).codeName.toLowerCase() != name.toLowerCase())
          println("WARNING: codeName should be changed to a consistent name: " + name + " vs. " + DerivationInfo.ofCodeName(name).codeName)
      } catch {
        case _: IllegalArgumentException => println("WARNING: codeName not found: " + name)
      }
    }

    /** Creates a named tactic */
    def by(t: BelleExpr): BelleExpr = new NamedTactic(name, t)

    def byTactic(t: ((ProvableSig, Position, Position) => BelleExpr)) = new DependentTwoPositionTactic(name) {
      override def computeExpr(p1: Position, p2: Position): DependentTactic = new DependentTactic("") {
        override def computeExpr(p: ProvableSig) = t(p, p1, p2)
      }
    }

    /** Creates a dependent position tactic without inspecting the formula at that position */
    //@todo why does this have to have a DependentPositionTactic instead of a PositionalTactic?
    def by(t: (Position => BelleExpr)): DependentPositionTactic = new DependentPositionTactic(name) {
      override def factory(pos: Position): DependentTactic = new DependentTactic(name) {
        override def computeExpr(provable: ProvableSig): BelleExpr = t(pos)
      }
    }

    /** Creates a dependent position tactic while inspecting the sequent/formula at that position */
    def by(t: ((Position, Sequent) => BelleExpr)): DependentPositionTactic = new DependentPositionTactic(name) {
      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = {
          require(pos.isIndexDefined(sequent), "Cannot apply at undefined position " + pos + " in sequent " + sequent)
          t(pos, sequent)
        }
      }
    }

    def byWithInputs(inputs: List[Expression], t: ((Position, Sequent) => BelleExpr)): DependentPositionWithAppliedInputTactic = new DependentPositionWithAppliedInputTactic(name, inputs) {
      override def factory(pos: Position): DependentTactic = new SingleGoalDependentTactic(name) {
        override def computeExpr(sequent: Sequent): BelleExpr = {
          require(pos.isIndexDefined(sequent), "Cannot apply at undefined position " + pos + " in sequent " + sequent)
          t(pos, sequent)
        }
      }
    }

    def byWithInput(input: Expression, t: ((Position, Sequent) => BelleExpr)): DependentPositionWithAppliedInputTactic =
      byWithInputs(List(input), t)

    /** Creates a dependent tactic, which can inspect the sole sequent */
    def by(t: Sequent => BelleExpr): DependentTactic = new SingleGoalDependentTactic(name) {
      override def computeExpr(sequent: Sequent): BelleExpr = t(sequent)
    }

    /** Creates a BuiltInRightTactic from a function turning provables and succedent positions into new provables.
      * @example {{{
      *         "andR" by((pr,pos)=> pr(AndRight(pos.top),0))
      *         }}}
      */
    def by(t: (ProvableSig, SuccPosition) => ProvableSig): BuiltInRightTactic = new BuiltInRightTactic(name) {
      override def computeSuccResult(provable: ProvableSig, pos: SuccPosition): ProvableSig = {
        requireOneSubgoal(provable, name)
        t(provable, pos)
      }
    }

    /** Creates a BuiltInLeftTactic from a function turning provables and antecedent positions into new provables.
      * @example {{{
      *         "andL" by((pr,pos)=> pr(AndLeft(pos.top),0))
      *         }}}
      */
    def by(t: (ProvableSig, AntePosition) => ProvableSig): BuiltInLeftTactic = new BuiltInLeftTactic(name) {
      override def computeAnteResult(provable: ProvableSig, pos: AntePosition): ProvableSig = {
        requireOneSubgoal(provable, name)
        t(provable, pos)
      }
    }

    /** Creates a BuiltInTwoPositionTactic from a function turning provables and two positions into new provables.
      * @example {{{
      *         "andL" by((pr,pos)=> pr(AndLeft(pos.top),0))
      *         }}}
      */
    def by(t: (ProvableSig, Position, Position) => ProvableSig): BuiltInTwoPositionTactic = new BuiltInTwoPositionTactic(name) {
      override def computeResult(provable: ProvableSig, pos1: Position, pos2: Position): ProvableSig = {
        requireOneSubgoal(provable, name)
        t(provable, pos1, pos2)
      }
    }
  }

  def anon(t: ((Position, Sequent) => BelleExpr)) = "ANON" by t
  def anon(t: (Sequent => BelleExpr)) = "ANON" by t

}

/**
 * @author Nathan Fulton
 */
//object Legacy {
//  /** The default mechanism for initializing KeYmaeraScheduler, Mathematica, and Z3 that are used in the legacy tactics.
//    * @note This may interfere in unexpected ways with sequential tactics.
//    */
//  def defaultInitialization(mathematicaConfig:  Map[String,String]) = {
//    Tactics.KeYmaeraScheduler = new Interpreter(KeYmaera)
//    Tactics.MathematicaScheduler = new Interpreter(new Mathematica)
//
//    Tactics.KeYmaeraScheduler.init(Map())
//    Tactics.Z3Scheduler.init
//    Tactics.MathematicaScheduler.init(mathematicaConfig)
//  }

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
//
//  def initializedScheduledTactic(mathematicaConfig : Map[String,String], tactic: keymaerax.tactics.Tactics.Tactic) = {
//    defaultInitialization(mathematicaConfig)
//    scheduledTactic(tactic)
//  }
//
//  def scheduledTactic(tactic : keymaerax.tactics.Tactics.Tactic) = new BuiltInTactic(s"Scheduled(${tactic.name})") {
//    //@see [[Legacy.defaultInitialization]]
//    if(!Tactics.KeYmaeraScheduler.isInitialized)
//      throw new BelleThrowable("Need to initialize KeYmaera scheduler and possibly also the Mathematica scheduler before running a Legacy.ScheduledTactic.")
//
//    override def result(provable: Provable): Provable = {
//      //@todo don't know if we can create a proof node from a provable.
//      if(provable.subgoals.length != 1) throw new Exception("Cannot run scheduled tactic on something with more than one subgoal.")
//
//      val node = new keymaerax.tactics.RootNode(provable.subgoals.head)
//
//      Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, node))
//
//      node.provableWitness
//    }
//  }
//}