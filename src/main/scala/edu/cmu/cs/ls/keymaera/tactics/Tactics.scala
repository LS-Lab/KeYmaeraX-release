/**
 * *****************************************************************************
 * Copyright (c) 2014 Jan-David Quesel, Marcus Völp
 *
 * Contributors:
 *     Jan-David Quesel - initial API and implementation
 *     Marcus Völp      - parallel execution framework
 * ****************************************************************************
 */
package edu.cmu.cs.ls.keymaera.tactics

//import scala.Option.option2Iterable
import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.core.Tool
import edu.cmu.cs.ls.keymaera.core.Config._
//import scala.Left
//import scala.Right
//import scala.Some
import scala.Unit
import scala.math.Ordered
import scala.collection.mutable.SynchronizedQueue
import scala.annotation.elidable
import scala.annotation.elidable._

import scala.language.implicitConversions

/**
 * @author jdq
 *
 */
/*
object Tactics {

//  trait Timeout;
//  val timeout = new Timeout {};

  // implicit conversions
  //implicit def immutableList2OptionList[T](l: ImmutableList[T]): Option[List[T]] = if (l.isEmpty) None else Some(l)

  //implicit def immutableList2List[T](l: ImmutableList[T]): List[T] = (for (i <- l.iterator) yield i).toList

//  implicit def ogl2Left(l: Option[Seq[ProofNode]]): Either[Option[Seq[ProofNode]], Timeout] = Left(l)

//  implicit def timeout2Right(l: Timeout): Either[Option[Seq[ProofNode]], Timeout] = Right(l)

  implicit def elgt2eolgt(l: Either[Seq[ProofNode], Timeout]): Either[Option[Seq[ProofNode]], Timeout] = l match {
    case Left(x) => Left(Some(x))
    case Right(x) => Right(x)
  }

  implicit def tactic2lazy(t: Tactic): () => Tactic = () => t

  def listOfLefts[A, B](l: Seq[Either[A, B]]): Seq[A] = l collect { case Left(x: A) => x }

  type RuleNumberLimit = Option[Int]

  type TimeLimit = Option[Long]

  class Limit(rl: RuleNumberLimit, tl: TimeLimit) {
    var rulesApplied = 0
    val initialTime = System.currentTimeMillis
    def limitHit: Boolean = (rl match {
      case Some(i) => i > rulesApplied
      case None => false
    }) || (tl match {
      case Some(i) => (System.currentTimeMillis - initialTime > i * 1000)
      case None => false
    })
    def timeLeft: TimeLimit = tl match {
      case None => None
      case Some(i) => Some(System.currentTimeMillis - initialTime)
    }
    def ++ : Unit = rulesApplied += 1
  }

  trait TacticConstructor {
    def getTactic: Tactic;
    def getName: String;
  }

  // A tactic is a script that applies specific rules to a goal
  // it can be built up using the usual constructs like sequential composition,
  // choice, repetition and other helper functions for conditional execution.
  // Further there are methods for generating terms/programelements that will be used
  // to instantiate schema variables in the rules.
  abstract class Tactic(val name: String, val root : ProofNode) {
    var result : Seq[ProofNode]

/*    extends ((ProofNode, Limit) => Either[Option[Seq[ProofNode]], Timeout]) { */

    // repeat tactic until a fixed point is reached
    def * : Tactic = repeatT(this)
    // apply the first tactic applicable
    def |(o: () => Tactic): Tactic = eitherT(this, o)
    // t1 ~ t2 = (t1 & t2) | t2
    def ~(o: () => Tactic): Tactic = composeBothT(this, o)
    // execute this tactic and the given tactics on the resulting branches
    def &(o: (() => Tactic)*): Tactic = composeT(this, o: _*)
    // create an or-branch for each given tactic
    def <(tcts: (() => Tactic)*) = branchT((() => this) :: tcts.toList: _*)
    override def toString: String = name

    def apply(tool : Tool) {}
  

//  abstract class PositionTactic(val name: String) extends (Position => Tactic) {
//    def applies(s: Sequent, p: Position): Boolean
//  }

  def repeatT(t: Tactic): Tactic = new Tactic("repeat " + t.toString) {
    def apply(g: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = {
      val app = (x: ProofNode) => apply(x, l)
      t(g, l) match {
        case x @ Right(_) => x // timeout
        // case branch closed
        case Left(None) => None
        // case a single goal, check if something changed
        // if we reached a fixed point, return
        case Left(Some(List(ng))) if (ng == g) => Some(List(g))
        // changed goals
        case Left(Some(goals)) =>
          val result = goals.map(app)
          if (result.contains(Right(timeout))) Right(timeout)
          else {
            val res = listOfLefts(result).flatten.flatten
            if (res.isEmpty) None else Some(res)
          }
      }
    }
  }

  /**
   * Apply t1 and if it changed something apply t2 afterwards
   */
  // execute tactic t on the current goal, for ts = (t1,t2,t3): execute t1 on the first goal, t2 on the second, and t3 on the rest
  def composeT(t: Tactic, ts: (() => Tactic)*): Tactic = new Tactic("compose " +
    t.toString + " -> " + ts.toString) {
    def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = {
      // create a stream that contains the elements of the given sequence and repeats the last one infinitly often
      def stutter[A](idx: Int, lst: Seq[A]): Stream[A] = Stream.cons(lst(idx), stutter(math.min(idx + 1, lst.length), lst))
      println("Applying " + name)
      t(p, l) match {
        // timeout
        case x @ Right(_) => x
        // case branch closed
        case x @ Left(None) => x
        // the first tactic could not be applied, therefore stop here
        case r @ Left(Some(Seq(ng))) if (ng == p) => r
        // case goals returned, execute t1 on the first one and t2 on tail.head and t3 on the rest
        case Left(Some(goals)) =>
          // apply ts.head to the first goal, ts.tail.head to the second and so on.
          // Apply ts.last to the remainder of the goals
          val result = stutter(0, ts).zip(goals).map(x => x._1()(x._2, l)).take(math.min(ts.length, goals.length)).toList
          if (result.contains(Right(timeout))) Right(timeout)
          else {
            val res = listOfLefts(result).flatten.flatten
            if (res.isEmpty) Left(None) else Some(res)
          }
      }
    }
  }

  def composeBothT(t1: Tactic, t2: () => Tactic): Tactic = (t1 & t2) | t2

  /**
   * Try to apply t1 and if it is not applicable try t2
   */
  def eitherT(t1: Tactic, t2: () => Tactic) = new Tactic("either " + t1 + " or " + t2) {
    def apply(g: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = {
      // apply t1
      t1(g, l) match {
        // case branch closed
        case Left(None) => None
        // case a single goal, check if something changed
        // if nothing changed try t2
        case Left(Some(List(ng))) if (ng == g) => t2()(g, l)
        // something was changed by t1 or we have a timeout
        case a => a
      }
    }
  }

  // spawn one or-branch per given tactic and persue the tactic on the respective branch
  def branchT(tcts: (() => Tactic)*): Tactic = new Tactic("branch") {
    def apply(p: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = ???/*{
      if (g.node.isClosed) return None
      val gs = g.apply(new BuiltInRuleApp(new OrBranchRule(tcts.size),
        new PosInOccurrence(g.node.sequent.iterator.next, PosInTerm.TOP_LEVEL, false),
        Constraint.TOP)).reverse
      val branches = gs.toArray(new Array[Goal](gs.size))
      assert(branches.size == tcts.size)
      val res = for (i <- 0 until tcts.size)
        yield tcts(i)()(branches(i), s, am.clone(branches(i)), l) match {
        case Left(Some(goals)) => goals
        case Left(None) => return None // one of the Or-Branches is already closed
        // if there was a timeout we ignore the result
      }
      if (res.size > 0) Some(res.toList.flatten) else None
    }*/
  }

  def NilT: Tactic = new Tactic("Nil") {
    def apply(g: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = {
      Some(List(g))
    }
  }

  def ifT(cond: ProofNode => Boolean, t: Tactic): Tactic = ifElseT(cond, t, NilT)
  //def ifT(cond: Sequent => Boolean, t: Tactic): Tactic = ifElseT(cond, t, NilT)

  def ifElseT(cond: ProofNode => Boolean, t: Tactic, ot: Tactic): Tactic = new Tactic("conditional " + t + " else " + ot) {
    def apply(g: ProofNode, l: Limit): Either[Option[Seq[ProofNode]], Timeout] = {
      if (cond(g)) t(g, l) else ot(g, l)
    }
  }
  //def ifElseT(cond: Sequent => Boolean, t: Tactic, ot: Tactic): Tactic = ifElseT(((p: ProofNode) => cond(p.sequent)), t, ot)


  /*
  def testT3: Tactic = (testT2 < (testT2 ~ cutT((_, _) => Some(Left(TermBuilder.DF.tt))))) ~ dlstrategy

  def testT: Tactic = dlstrategy

  //def testT: Tactic = TacticLoader.loadTactic(new File("/tmp/Test.scala")).getTactic

  def testTp: Tactic = ((testT2 | tryheuristicT("alpha") | tryheuristicT("simplify_prog") | tryheuristicT("diff_solve"))*) ~ tryruleT(ReduceRule.INSTANCE.name.toString)

  def testT2: Tactic = (tryruleT("modality_split_right") | tryruleT("eliminate_variable_decl") | tryruleT(UpdateSimplificationRule.INSTANCE.name.toString))*

  def dlstrategy: Tactic = (((tryheuristicT("closure", "concrete",
      "alpha", "simplify_prog", "simplify", "diff_solve", "delta", "beta")) | loopInvT | loopTry)*) ~
    eliminateUniversalQuantifiersT
  //tryruleT(ReduceRule.INSTANCE.name.toString)

  def dlstrategyOrg: Tactic = (((tryruleT(UpdateSimplificationRule.INSTANCE.name.toString)
    | tryheuristicT("closure", "concrete",
      "alpha", "simplify_prog", "simplify", "delta", "beta") | diffSolveT) | loopInvT)*) ~
    eliminateUniversalQuantifiersT

  def eliminateUniversalQuantifiersT = tryruleT(MergeSequentRule.name.toString) ~ tryruleT(QuantifyAllSkolemSymbolsRule.name.toString) ~ tryruleT("reduce_form_right") ~ tryruleT("close_by_true")

  def run(t: Tactic, g: Goal, s: Services) = t(g, s, new DLRuleAppManager, new Limit(None, None))

  def run(t: Tactic, goals: ImmutableList[Goal], s: Services) =
    for (g <- immutableList2List(goals))
      t(g, s, new DLRuleAppManager, new Limit(None, None))

  def timeoutT(t: Tactic, rl: RuleNumberLimit, tl: TimeLimit): Tactic = new Tactic("timeout " + t) {
    def apply(g: Goal, s: Services, am: AppManager, u: Limit): Either[Option[List[Goal]], Timeout] = t(g, s, am, new Limit(rl, tl))
  }
  */

  // interface for generating instances
  type Generator[T] = ((Rule, ProofNode, String) => Option[T])

  // creates a new branch and evaluates t, then evaluates t on the other branch
  // this assumes that t has a state that changes during each execution and will
  // eventually halt
  def branchRepeatT(t: Tactic): Tactic = branchT(t, () => branchRepeatT(t))


*/

object Tactics {

  val KeYmaeraScheduler = new Scheduler(Seq.fill(Config.maxCPUs)(KeYmaera))



  class Stats(var executionTime : Int, var branches : Int, var rules : Int) {
    var tacs : Int = 0

    def this() = this(0, 0, 0)

    def measure[B](fn : => B) : B = {
      val start = System.currentTimeMillis
      val res = fn
      executionTime = executionTime + ((start - System.currentTimeMillis) / 1000).toInt
      return res
    }

    def incTacs() { tacs = tacs + 1 }

    def incRule() { rules = rules + 1 }

    def incBranch(n : Int) { branches = branches + n }

    def clear() {
      rules         = 0
      branches      = 0
      executionTime = 0
    }
  }

  val nilStats : Stats = new Stats(0, 0, 0)

  class Limits(val parent   : Limits,
               var timeout  : Option[Int],
               var branches : Option[Int],
               var rules    : Option[Int]) {

    def min(x : Option[Int], y : Option[Int]) : Option[Int] = {
      x match {
        case Some(valX) =>
          y match {
            case Some(valY) => if (valX < valY) Some(valX) else Some(valY)
            case None       => Some(valX)
          }
        case None => y
      }
    }

    if(parent != null) {
      timeout = min(timeout, parent.timeout)
      branches = min(branches, parent.branches)
      rules = min(rules, parent.rules)
    }

    def this(t : Option[Int], b : Option[Int], r : Option[Int]) = this(null, t, b, r)

    def checkLocal(s : Stats) : Boolean = 
      (timeout match {
        case Some(tVal) => s.executionTime > tVal
        case None       => false
      }) ||
      (branches match {
        case Some(bVal) => s.branches > bVal
        case None       => false
      }) ||
      (rules match {
        case Some(rVal) => s.rules > rVal
        case None       => false
      })

    def update(s : Stats) : Boolean =
      this.synchronized {
        timeout match {
          case Some(tVal) => timeout = Some(tVal - s.executionTime)
          case None       =>
        }
        branches match {
          case Some(bVal) => timeout = Some(bVal - s.branches)
          case None       =>
        }
        rules match {
          case Some(rVal) => timeout = Some(rVal - s.rules)
          case None       =>
        }
        return checkLocal(nilStats)
      }

    def propagate(s : Stats) : Boolean = {
        var p = this
        var r = false
        while (p != null) r = p.update(s) || r
        s.clear()
        return r
    }

    def checkStats(s : Stats)(res : Status) : Status =
      if (s.executionTime > timeThres || s.branches > branchThres || s.rules > ruleThres) {
        // propagate updates through all limit objects
        if (propagate(s)) {
          return LimitExceeded
        } else {
          return res
        }
      } else {
        // check local breach only
        if (checkLocal(s)) {
          propagate(s)
          return LimitExceeded
        } else {
          return res
        }
      }
  }

  // fix me if you want to start with configurable default limit
  val defaultLimits : Limits = new Limits(None, None, None)

  abstract class Tactic(val name : String) extends Stats { 

    var scheduler : Scheduler = KeYmaeraScheduler

    var limit  : Limits = defaultLimits

    var continuation : (Tactic, Status, Seq[ProofNode]) => Unit = stop

    override def toString: String = name

    def applicable(node : ProofNode) : Boolean
    def apply  (tool : Tool, node : ProofNode)

    def inheritStats(s : Stats) {
      tacs          = s.tacs
      executionTime = s.executionTime
      branches      = s.branches
      rules         = s.rules
    }

    val priority : Int = 10

    def dispatch(t : Tactic, l : Limits, node : ProofNode) {
      inheritStats(t)
      limit = l
      scheduler.dispatch(new TacticWrapper(this, node))
    }

    def dispatch(t : Tactic, node : ProofNode) { dispatch(t, t.limit, node) }

    def checkStats(res : Status) : Status = limit.checkStats(this)(res)

    /**
     * Convenience wrappers
     */
  /*
    // repeat tactic until a fixed point is reached
    def * : Tactic = repeatT(this)
    // apply the first tactic applicable
    def |(o: () => Tactic): Tactic = eitherT(this, o)
    // t1 ~ t2 = (t1 & t2) | t2
    def ~(o: () => Tactic): Tactic = composeBothT(this, o)
    // execute this tactic and the given tactics on the resulting branches
    def &(o: (() => Tactic)*): Tactic = composeT(this, o: _*)
    // create an or-branch for each given tactic
    def <(tcts: (() => Tactic)*) = branchT((() => this) :: tcts.toList: _*)
  */
  }

  /**
   * do nothing
   */
  def NilT = new Tactic("Nil") {
    def applicable(node : ProofNode) = true
    def apply(tool : Tool, node : ProofNode) = {
      continuation(this, Success, Seq(node))
    }
  }

  def stop(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    tFrom.limit.propagate(tFrom)
    result.foreach(n => n.checkParentClosed())
  }

  def onSuccess(tNext : Tactic)(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    if (status == Success) result.foreach((n : ProofNode) => tNext.dispatch(tFrom, n))
  }

  def unconditionally(tNext : Tactic)(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    result.foreach((n : ProofNode) => tNext.dispatch(tFrom, n))
  }

  def onChange(n : ProofNode, tNext : Tactic)(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    if (Seq(n) != result) result.foreach((n : ProofNode) => tNext.dispatch(tFrom, n))
  }

  def onNoChange(n : ProofNode, tNext : Tactic)(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    if (Seq(n) == result) tNext.dispatch(tFrom, n)
  }

  def onChangeAndOnNoChange(n : ProofNode, tChange : Tactic, noChange: (Tactic, Status, Seq[ProofNode]) => Unit)(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    if (Seq(n) == result) noChange(tFrom, status, result)
    else result.foreach((pn: ProofNode) => tChange.dispatch(tFrom, pn))
  }


  def seqT(left : Tactic, right : Tactic) =
    new Tactic("Seq(" + left.name + "," + right.name + ")") {
      def applicable(node : ProofNode) = left.applicable(node)

      def apply(tool : Tool, node : ProofNode) = {
        right.continuation = continuation
        left.continuation  = onSuccess(right)
        left.dispatch(this, node)
      }
    }

  def eitherT(left : Tactic, right : Tactic) =
    new Tactic("Seq(" + left.name + "," + right.name + ")") {
      def applicable(node : ProofNode) = left.applicable(node)

      def apply(tool : Tool, node : ProofNode) = {
        right.continuation = continuation
        left.continuation = onNoChange(node, right)
        left.dispatch(this, node)
      }
    }

  def weakSeqT(left : Tactic, right : Tactic) =
    new Tactic("WeakSeq(" + left.name + "," + right.name + ")") {
      def applicable(node : ProofNode) = left.applicable(node)

      def apply(tool : Tool, node : ProofNode) = {
        right.continuation = continuation
        left.continuation  = unconditionally(right)
        left.dispatch(this, node)
      }
    }

  def ifElseT(cond : ProofNode => Boolean, thenT : Tactic, elseT : Tactic) =
    new Tactic("Conditional " + thenT + " else " + elseT) {
      def applicable(node : ProofNode) = true

      def apply(tool : Tool, node : ProofNode) = {
        if (cond(node)) {
           thenT.continuation = continuation
           thenT.dispatch(this, node)
        } else {
           elseT.continuation = continuation
           elseT.dispatch(this, node)
        }
      }
    }

  def ifT(cond : ProofNode => Boolean, thenT : Tactic) =
      ifElseT(cond, thenT, NilT)

  // def branchT(tcts: (() => Tactic)*): Tactic = new Tactic("branch")
  // def branchRepeatT(t: Tactic): Tactic = branchT(t, () => branchRepeatT(t))
  def repeatT(t: Tactic): Tactic = new Tactic("Repeat(" + t.name + ")") {
    def applicable(node: ProofNode) = t.applicable(node)

    def apply(tool: Tool, node: ProofNode) = {
      t.continuation = onChangeAndOnNoChange(node, this, continuation)
      println("Dispatching " + t.name)
      t.dispatch(this, node)
    }
  }


  /********************************************************************************
   * Rule application
   ********************************************************************************
   */

  /**
   * Apply rule
   */
  abstract class ApplyRule(val rule : Rule) extends Tactic("Apply rule " + rule) {

    def apply(tool : Tool, node : ProofNode) {
      println("Trying to apply " + rule)
      if (applicable(node)) {
        incRule()
        val res = measure(node(rule))
        continuation(this, checkStats(Success), res)
      } else {
        continuation(this, Failed,  Seq(node))
      }
    }

  }

  /**
   * Apply position rule
   */
  abstract class ApplyPositionRule(val rule : PositionRule, val pos : Position)
                                            extends Tactic("Apply rule " + rule) {

    def apply(tool : Tool, node : ProofNode) {
      if (applicable(node)) {
        incRule()
        val res = measure(node(rule, pos))
        continuation(this, checkStats(Success), res)
      } else {
        continuation(this, Failed,  Seq(node))
      }
    }

  }

  /**
   * Apply position rule
   */
  abstract class ApplyAssumptionRule(val rule : AssumptionRule,
                                     val aPos : Position, val pos : Position)
                                            extends Tactic("Apply rule " + rule) {

    def apply(tool : Tool, node : ProofNode) {
      if (applicable(node)) {
        incRule()
        val res = measure(node(rule, aPos, pos))
        continuation(this, checkStats(Success), res)
      } else {
        continuation(this, Failed,  Seq(node))
      }
    }

  }

}
