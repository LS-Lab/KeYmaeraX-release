/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * *****************************************************************************
 * Copyright (c) 2014 Jan-David Quesel, Marcus Völp
 *
 * Contributors:
 *     Jan-David Quesel - initial API and implementation
 *     Marcus Völp      - parallel execution framework
 * ****************************************************************************
 */
package edu.cmu.cs.ls.keymaerax.tactics

import ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.core._
import Config._
import edu.cmu.cs.ls.keymaerax.tactics.TacticLibrary.TacticHelper
import edu.cmu.cs.ls.keymaerax.tools._
import scala.Unit
import scala.language.implicitConversions
import scala.collection.mutable.HashMap
import scala.collection.mutable
import java.util.concurrent.ConcurrentLinkedQueue

/**
 * @author jdq
 * @author Andre Platzer
 */

/**
 * Programming Guide
 * ==================
 * Tactics follow a continuation-style programming model. That is, each
 * tactic is an executable entities with a continuation function, which
 * gets executed after the tactics completes. For example, SeqT is a
 * tactics which combines two embedded tactics: left and right. Right is
 * executed after left completes successfully. Therefore, SeqT dispatches
 * left and registers onSuccess as a continuation function. Once left
 * completes, the tactics executor invokes onSuccess, which checks the
 * result of left and dispatches right if left is
 * successful. Continuation functions are executed immediately after the
 * tactic. Therefore, long running operations should all be encapsulated
 * into tactics and continutations should be limited to simple checks and
 * the dispatching of further tactics. Once dispatched tactics are
 * assumed to be self contained and may be executed in parallel.
 *
 * Overview
 * ========
 * The tactics framework consists of the following modules:
 * - abstract class Tactic: defines tactic to execute (by invoking apply)
 * - object Tactics:        tactic definitions and convenience wrappers
 * - class TacticExecutor:  thread that executes tactics
 * - class Scheduler:       collection of threads (e.g., per tool) plus queue of ready to
 *                          execute tactics. Tactics are dispatched to a scheduler (e.g.,
 *                          to the mathematica scheduler). Once dispatched, a free thread
 *                          of this scheduler (e.g., the thread which corresponds to a free
 *                          mathematica kernel) picks the highest prioritized dispatched
 *                          tactics and executes it until a limit is exceeded or until it
 *                          completes. After that, the continuation of the tactic is
 *                          executed.
 * - class TacticWrapper:   helper class to combine tactics with the proof nodes on which
 *                          they should be executed. Automatically created during dispatch.
 * - class Limits:          class to keep track and update limits (e.g., no of branches)
 */



/*
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

  // creates a new branch and evaluates t, then evaluates t on the other branch
  // this assumes that t has a state that changes during each execution and will
  // eventually halt
  def branchRepeatT(t: Tactic): Tactic = branchT(t, () => branchRepeatT(t))


*/
// TODO: In order to stop execution we should explicitly schedule a "checkStop" tactic to react on that signal
// for example a valid point to stop is after some loop unrolling. If we just stop at an arbitrary point we run into
// the issue, that that might not be a valid point to ever resume the tactic (e.g., we have stopped right before
// a uniform substitution or something (this was different for KeYmaera 3 where the strategy was stateless).
// TODO: clearly mark exit points of tactics to give a & (b, c) a well defined meaning over complex tactics instead of just rule applications
object Tactics {

  // TODO replace with dependency injection
  var KeYmaeraScheduler = new Interpreter(KeYmaera)//new Scheduler(Seq.fill(Config.maxCPUs)(KeYmaera))
  var MathematicaScheduler = new Interpreter(new Mathematica)
  var Z3Scheduler  : Option[Interpreter] = try { Some(new Interpreter(new Z3)) } catch { case e : Exception => None }
  var PolyaScheduler : Option[Interpreter] = try { Some(new Interpreter(new Polya)) } catch { case e : Exception => None }
    //new Scheduler(for (i <- 0 until Config.mathlicenses) yield new Mathematica)

  class Stats(var executionTime : Int, var branches : Int, var rules : Int) {
    var tacs : Int = 0

    def this() = this(0, 0, 0)

    /**
     * measure execution time of function fn
     * invoked by ApplyRule Tactic
     */
    def measure[B](fn : => B) : B = {
      val start = System.currentTimeMillis
      val res = fn
      executionTime = executionTime + ((start - System.currentTimeMillis) / 1000).toInt
      return res
    }

    /**
     * increase no of executed tactics
     */
    def incTacs() { tacs = tacs + 1 }

    /**
     * increase no of applied rules
     */
    def incRule() { rules = rules + 1 }

    /**
     * increase no of branches (e.g., and / or splits)
     */
    def incBranch(n : Int) { branches = branches + n }

    /**
     * clear tactic stats
     */
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
        // FIXME: what was the intention of this loop? It's an infinite loop like this (therefore commented out for now)
        // FIXME: update stats all the way up the tactics tree; check whether this is a data-race with delete ops before adding p = p.parent and reenabling the loop.
        /*while (p != null)*/ r = p.update(s) || r
        s.clear()
        return r
    }

    /**
     * check limits for given tactic
     * ===
     * If a limit exceeds a threshold values, all statistics are propagated to upper nodes.
     * This way, overruns are detectable across branches, although with limited granularity.
     */
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

  type Continuation = (Tactic, Status, Seq[ProofNode]) => Unit

  /**
   * A schedulable tactic that can be applied to try to prove a ProofNode.
   */
  abstract class Tactic(val name : String) extends Stats {

    /** The scheduler that is running this tactic */
    var scheduler: ExecutionEngine = KeYmaeraScheduler

    /** The resource limits to which this tactic is restricted */
    var limit  : Limits = defaultLimits

    /** Continuation function to execute after applying this tactic returns */
    var continuation : Continuation = stop

    override def toString: String = name

    /** Returns true if this tactics is applicable to the proof node */
    def applicable(node : ProofNode) : Boolean
    /** Apply this tactic to the given node using the given tool (e.g., a specific mathematica kernel) */
    def apply  (tool : Tool, node : ProofNode)

    def inheritStats(s : Stats) { // adopt stats (e.g., from privious tactic)
      tacs          = s.tacs
      executionTime = s.executionTime
      branches      = s.branches
      rules         = s.rules
    }

    val priority : Int = 10

    /**
     * The root tactic is passed on via dispatches.
     */
    var root : Option[Tactic] = None

    /**
     * We will always use the root's updateInfo method
     */
    var updateInfo: (ProofNodeInfo => Unit) = (_: ProofNodeInfo) => ()
    var updateStepInfo: (ProofStepInfo => Unit) = (_: ProofStepInfo) => ()

    /**
     * This is defined for the root only; in other words, the following should be 
     * an object invariant (that not being root implies runningTactics is empty):
     * (this != root && runningTactics.isEmpty) || (this==root)
     * 
     */
    private val runningTactics : ConcurrentLinkedQueue[Tactic] = new ConcurrentLinkedQueue()

    //It should be the case that runningTactics.isEmpty IFF the scheduler is idle.
     
    /**
     * @return true if this tactic is complete.
     */
    val isComplete = root match {
      case None => this.runningTactics.contains(this)
      case Some(x) => !x.runningTactics.contains(this)
    }

    def unregister: Unit = root match {
      case None => unregister(this)
      case Some(x) => x.unregister(this)
    }

    protected def unregister(t : Tactic): Unit = root match {
      case None =>
        runningTactics.remove(t)
//        println("removing " + t.name + " from running tactics. Remaining: " + runningTactics.size)
        // if there are no more running tactics notify our listeners
        if(runningTactics.isEmpty) {
          val theListeners = listeners
          listeners = Nil
          theListeners.foreach(_(this))
        }
      case Some(x) => x.unregister(t)
    }

    def registerRunningTactic(t : Tactic) : Unit = {
      root match {
        case None =>
          runningTactics.add(t)
//          println("register " + t.name + " as running. Remaining: " + runningTactics.size)
        case Some(x) => assert(x != this); x.registerRunningTactic(t)
      }
    }

    var listeners: List[Tactic => Unit] = Nil

    def registerCompletionEventListener(e: (Tactic => Unit)) {
      require(root == None, "Only the root should have listeners")
      this.synchronized {
        listeners = listeners :+ e
      }
    }

    /**
     * Dispatch this tactic as a child of the parent tactic to the given proof node within the given resource limits.
     * @param parent - parent tactic
     */
    def dispatch(parent : Tactic, l : Limits, node : ProofNode) {
      inheritStats(parent)
      limit = l
      this.root = if(parent != this && parent.root == None) Some(parent) else parent.root
      require(parent.root != Some(this), "Cannot have loops in tactic tree")
      registerRunningTactic(this)
      if (scheduler == null)
        throw new IllegalStateException("Cannot schedule tactics " + this + " in absence of an appropriate scheduler. Create and initialize the scheduler first.")
      scheduler.dispatch(new TacticWrapper(this, node))
    }

    /** Dispatch this tactic as a child of parent to the given proof node within the parent's limits. */
    def dispatch(parent : Tactic, node : ProofNode) { dispatch(parent, parent.limit, node) }

    def checkStats(res : Status) : Status = limit.checkStats(this)(res)

    /**
     * Convenience wrappers
     */
    /**
     * repeat tactic until a fixed point is reached
     */
    def * : Tactic = repeatT(this)
    /**
     * repeat tactic n times
     */
    def *(n: Int): Tactic = {
      require(n>=0, "Repeat non-negative number of times")
      if (n > 0) this & this*(n-1) else NilT
    }
    /**
     * apply the first tactic applicable
     */
    def |(o: Tactic): Tactic = eitherT(this, o)
    /**
     * Sequential composition: execute this tactic and the given tactics in this order on the resulting branches.
    */
    def &(a: Tactic, o: Tactic*): Tactic = seqComposeT(this, a, o: _*)
    def &&(a: Tactic, o: Tactic*): Tactic = seqComposeExactT(this, a, o: _*)
    def &&(o : List[Tactic]): Tactic = seqComposeExactListT(this, o)

    /**
     * Weak sequential composition if possible.
     * Execute the given tactics in that order if possible: t1 ~ t2 = (t1 & t2) | t2
     */
    def ~(o: Tactic): Tactic = weakSeqT(this, o)
    /**
     * create an or-branch for each given tactic
     */
    def <(tcts: Tactic*) = branchT(this :: tcts.toList: _*)
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
  def NilPT = new PositionTactic("Nil") {
    def applies(s: Sequent, p: Position): Boolean = true
    def apply(p: Position): Tactic = NilT
  }

  /**
   * Stop tactics execution.
   * @TODO Implement and check.
   */
  def stopT = new Tactic("Stop") {
    def applicable(node : ProofNode) = true
    def apply(tool : Tool, node : ProofNode) = {}
  }

  /**
   * Error tactics execution.
   * @TODO Implement and check.
   */
  def errorT(msg: String) = new Tactic("Error") {
    def applicable(node : ProofNode) = true
    def apply(tool : Tool, node : ProofNode) = {println(msg + "\nat " + node.sequent); throw new TacticException(msg, node)}
  }

  /**
   * Assertion Tactic, which has no effect except to sanity-check the given condition like an assert would.
   */
  def assertT(cond : Sequent=>Boolean, msg:String = ""): Tactic = ifT(node => !cond(node.sequent), errorT("Tactic Assertion failed: " + msg))

  /**
   * Assertion Tactic, which checks that the given formula is present at the given position in the sequent that this tactic is applied to.
   */
  def assertT(formulaExpectedAtPosition: Formula, pos: Position, msg:String): Tactic = assertT(s=>s(pos)==formulaExpectedAtPosition, "Expected: " + formulaExpectedAtPosition.prettyString + "at position " + pos + " " + msg)
  
  def assertT(formulaExpectedAtPosition: Formula, pos: Position): Tactic = assertT(formulaExpectedAtPosition, pos, "")


  /**
   * Assertion PositionTactic, which has no effect except to sanity-check the given condition like an assert would.
   */
  def assertPT(cond : (Sequent,Position)=>Boolean, msg:String = ""): PositionTactic = new PositionTactic("Assert") {
    def applies(s: Sequent, p: Position) = true

    def apply(pos: Position): Tactic = ifT(node => !cond(node.sequent, pos), errorT("Tactic Assertion failed: " + msg + " at " + pos))
  }
  
  /**
   * Assertion PositionTactic, which checks that the given formula is present at the position in the sequent where this tactic is applied to.
   */
  def assertPT(formulaExpectedAtPosition: Formula, msg:String): PositionTactic =
    assertPT((s,pos)=> (if (pos.isAnte) s.ante.size > pos.index else s.succ.size > pos.index ) && s(pos)==formulaExpectedAtPosition, "Expected: " + formulaExpectedAtPosition.prettyString + " " + msg)

  def assertPT(formulaExpectedAtPosition: Formula): PositionTactic = assertPT(formulaExpectedAtPosition, "")

  def assertPT(termExpectedAtPosition : Term, msg : String): PositionTactic = assertPT((s,p) => {

    if(TacticHelper.getTerm(s, p) == termExpectedAtPosition) {
      true
    } else{
      println(" ---> About to fail an assertPT because we expected " + termExpectedAtPosition.prettyString + " but found " + TacticHelper.getTerm(s, p) + " <---")
      false
    }
  }, msg)

  /**
   * Assertion PositionTactic, which checks that the sequent has the specified number of antecedent and succedent formulas, respectively.
   */
  def assertT(antecedents: Int, succedents: Int): Tactic = assertT(s=>s.ante.length==antecedents && s.succ.length==succedents, "Expected: " + antecedents + " antecedent and " + succedents + " succedent formulas")


  def stop(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    tFrom.limit.propagate(tFrom)
    result.foreach(n => n.tacticInfo.checkParentClosed())
  }

  /*
  def onSuccess(tNext : Tactic)(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    if (status == Success) result.foreach((n : ProofNode) => tNext.dispatch(tFrom, n))
  }
  */

  def onSuccess(tNext : Tactic*)(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    if (status == Success && result.length > 0) {
      val len = math.max(tNext.length, result.length)
      def cont[A](s: Seq[A]) = Stream.continually(s).flatten.take(len).toList
      for ((t, n) <- cont(tNext) zip cont(result)) t.dispatch(tFrom, n)
    }
  }

  def onSuccessExact(tNext : Tactic*)(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    if (status == Success) {
      if (tNext.length == result.length) {
        for ((t, n) <- tNext zip result) t.dispatch(tFrom, n)
      }
    }
  }

  def unconditionally(tNext : Tactic*)(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    if(result.length > 0) {
      val len = math.max(tNext.length, result.length)
      def cont[A](s: Seq[A]) = Stream.continually(s).flatten.take(len).toList
      for ((t, n) <- cont(tNext) zip cont(result)) t.dispatch(tFrom, n)
    }
  }

  def onChange(n : ProofNode, tNext : Tactic)(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    if (Seq(n) != result) result.foreach((n : ProofNode) => tNext.dispatch(tFrom, n))
  }

  def onNoChange(n : ProofNode, tNext : Tactic)(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    if (Seq(n) == result) tNext.dispatch(tFrom, n)
  }

  def onChangeAndOnNoChange(n : ProofNode, change: Continuation, noChange: Continuation)(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    if (Seq(n) == result) noChange(tFrom, status, result)
    else change(tFrom, status, result)
  }

  /**
   * dispatch left. If left returns successfully, dispatch right on the resulting proof node.
   */
  def seqT(left : Tactic, right : Tactic) =
    new Tactic("Seq(" + left.name + "," + right.name + ")") {
      def applicable(node : ProofNode) = left.applicable(node)

      def apply(tool : Tool, node : ProofNode) = {
        right.continuation = continuation
        left.continuation  = onSuccess(right)
        left.dispatch(this, node)
      }
    }

  
  /**
   * I have a bunch of tactics collected in the list ``r", rights = at least one tactic
   * For all the r tactics that are to be executed later on, continue with the 
   * current continuation of this tactic.
   * 
   * This is like scalar multiplcation???
   * 
   * The concept doesn't generalize to tactics well because in onSuccess, we 
   * somehow don't end up doing the right thing because we could end up with
   * multiple branches that are actually the same or something?
   * 
   * So the zip allows us to use repitition to never forget a single rule
   * or a single tactic.
   * 
   * The branch labels in this file are defined in tacticslibrary.
   */
  def seqComposeT(left: Tactic, right: Tactic, rights: Tactic*) =
    new Tactic("SeqComposeT(" + left.name + ", " + right + ", " + rights.map(_.name).mkString(", ") + ")") {
      def applicable(node : ProofNode) = left.applicable(node)

      def apply(tool : Tool, node : ProofNode) = {
        val r = right +: rights
        for (t <- r)
          t.continuation = continuation
        left.continuation = onSuccess(r: _*)
        left.dispatch(this, node)
      }
    }

  def seqComposeExactListT(left: Tactic, rights: List[Tactic]) =
    new Tactic("SeqComposeExactT(" + left.name + ", " + rights.map(_.name).mkString(", ") + ")") {
      assert(rights.length != 0)
      def applicable(node : ProofNode) = left.applicable(node)

      def apply(tool : Tool, node : ProofNode) = {
        val r = rights
        for (t <- r)
          t.continuation = continuation
        left.continuation = onSuccessExact(r: _*)
        left.dispatch(this, node)
      }
    }

   def seqComposeExactT(left: Tactic, right: Tactic, rights: Tactic*) =
    new Tactic("SeqComposeExactT(" + left.name + ", " + right.name + ", " + rights.map(_.name).mkString(", ") + ")") {
      def applicable(node : ProofNode) = left.applicable(node)

      def apply(tool : Tool, node : ProofNode) = {
        val r = right +: rights
        for (t <- r)
          t.continuation = continuation
        left.continuation = onSuccessExact(r: _*)
        left.dispatch(this, node)
      }
    }

   /**
    * Try left. 
    * 
    * If left is applicable and actually changes the node, quit and
    * execute the followup.
    * 
    * If left is not applicable (does not change the node), then try right.
    * 
    * Kind of like non-deterministic choice, although "the successful branch wins".
    */
  def eitherT(left : Tactic, right : Tactic): Tactic =
    new Tactic("Either(" + left.name + "," + right.name + ")") {
      def applicable(node : ProofNode): Boolean = left.applicable(node) || right.applicable(node)

      def apply(tool : Tool, node : ProofNode) = {
        right.continuation = continuation
        if(left.applicable(node)) {
            left.continuation = onChangeAndOnNoChange(node, continuation, onNoChange(node, right))
            left.dispatch(this, node)
          } else {
            right.dispatch(this, node)
        }
      }
    }

  /**
   * Continues regardless of the success of left.
   */
  def weakSeqT(left : Tactic, right : Tactic) =
    new Tactic("WeakSeq(" + left.name + "," + right.name + ")") {
      def applicable(node : ProofNode) = left.applicable(node) || right.applicable(node)

      def apply(tool : Tool, node : ProofNode) = {
        right.continuation = continuation
        if(left.applicable(node)) {
          left.continuation = unconditionally(right)
          left.dispatch(this, node)
        } else {
          right.dispatch(this, node)
        }
      }
    }

  /**
   * Allows decision making based upon the proof node (using code).
   */
  def ifElseT(cond : ProofNode => Boolean, thenT : Tactic, elseT : Tactic) =
    new Tactic("Conditional " + thenT + " else " + elseT) {
      def applicable(node : ProofNode) = if(cond(node)) thenT.applicable(node) else elseT.applicable(node)

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

  /**
   * Generalizes if-else. the generator can return the "do nothing" tactic.
   * Useful with the branch labels.
   */
  def switchT(generate: ProofNode => Tactic) = new Tactic("Switch") {
    def applicable(node : ProofNode) = generate(node).applicable(node)
    def apply(tool : Tool, node : ProofNode) = {
      val t = generate(node)
      t.continuation = continuation
      t.dispatch(this, node)
    }
  }

  /**
   * Dispatches a whole bunch of tactics on the same node.
   * This tactic might generate a lot of alternatives.
   */
  def branchT(tcts: Tactic*): Tactic = new Tactic("branch") {
    def applicable(node: ProofNode) = true

    def apply(tool: Tool, node: ProofNode) = {
      for(t <- tcts) {
        t.continuation = continuation
        t.dispatch(this, node)
      }
    }
  }

  /**
   * The smallest fixed point of t. 
   * Unloop the rule once. If the node changed, then do the loop again.
   * If the node is not changes, then continues with the follow-up
   */
  def repeatT(t: Tactic): Tactic = new Tactic("Repeat(" + t.name + ")") {
    def applicable(node: ProofNode) = true

    def apply(tool: Tool, node: ProofNode) = {
      if(t.applicable(node)) {
        val repeat = repeatT(t)
        repeat.continuation = continuation
        t.continuation = onChangeAndOnNoChange(node, onChange(node, repeat), continuation)
        t.dispatch(this, node)
      } else {
        continuation(this, Success, Seq(node))
      }
    }
  }

  // do left tactic with high priority, and right with low priority.
  // raise priority of right tactic when left finished

  /********************************************************************************
   * Rule application
   ********************************************************************************
   */

  /**
   * Base tactic that directly applies the given rule.
   */
  abstract class ApplyRule[R <: Rule](val rule : R) extends Tactic("Apply rule " + rule) {

    def apply(tool : Tool, node : ProofNode) {
      if (applicable(node)) {
        incRule()
        val res = measure(node(rule))
        // call updateInfo in order to propagate information along this proof node
        this.root match {
          case Some(r) =>
            r.updateStepInfo(res.tacticInfo)
            for(n <- res.subgoals) r.updateInfo(n.tacticInfo)
          case None =>
            this.updateStepInfo(res.tacticInfo)
            for(n <- res.subgoals) this.updateInfo(n.tacticInfo)
        }
        continuation(this, checkStats(Success), res.subgoals)
      } else {
        continuation(this, Failed,  Seq(node))
      }
    }

  }

  /**
   * A PositionTactic applied to a position results in a tactic that can be applied to a ProofNode.
   * {{{PositionTactic: Position => Tactic}}}
   * @todo split into type-safe LeftPositionTactic(AntePos) and RightPositionTactic(SuccPos)
   * @todo duplicate into 3 independent classes?
   *       abstract class LeftPositionTactic extends (AntePosition => Tactic) { def &(o:LeftPositionTactic) ... }
   *       abstract class RightPositionTactic extends (SuccPosition => Tactic) { def &(o:RightPositionTactic) ... }
   *       abstract class PositionTactic extends (Position => Tactic) { def &(o:PositionTactic) ... }
   * Downside: that will lead to dynamic checking for PositionTactic & LeftPositionTactic.
   */
  abstract class PositionTactic(val name: String) extends (Position => Tactic) {
    /** Checks whether this position tactic will be applicable at the indicated position of the given sequent */
    def applies(s: Sequent, p: Position): Boolean

    /** Apply this PositionTactic at the indicated Position to obtain a tactic to use at any ProofNode */
    def apply(signedPos: Int): Tactic = apply(Position.seqPos2Position(SeqPos(signedPos)))
    /** Apply this PositionTactic at the indicated Position to obtain a tactic to use at any ProofNode */
    def apply(signedPos: Int, posInExpr: List[Int]): Tactic = apply(Position.seqPos2Position(SeqPos(signedPos), posInExpr))
    /** Apply this PositionTactic at the indicated Position to obtain a tactic to use at any ProofNode */
    def apply(p: Position): Tactic

    /**
     * Sequential composition of PositionTactics applied at the same position.
     */
    def &(pt: PositionTactic) = new PositionTactic("Seq(" + this.name + ", " + pt.name) {
      override def applies(s: Sequent, p: Position): Boolean = PositionTactic.this.applies(s, p)

      //@TODO Unfortunately, this crucially relies on stable positions
      override def apply(p: Position): Tactic = PositionTactic.this.apply(p) & pt.apply(p)
    }

    def ~(pt: PositionTactic) = new PositionTactic("WeakSeq(" + this.name + ", " + pt.name) {
      override def applies(s: Sequent, p: Position): Boolean = PositionTactic.this.applies(s, p)

      //@TODO Unfortunately, this crucially relies on stable positions
      override def apply(p: Position): Tactic = PositionTactic.this.apply(p) ~ pt.apply(p)
    }

    //@todo duplicate compared to FormulaConverter.subFormulaAt
    @deprecated("Use FormulaConverter.subFormulaT instead")
    def formulaAtPosition(sequent : Sequent, position : Position) : Option[Formula] = {
      var formula : Option[Formula] = None
      val fn = new ExpressionTraversalFunction {
        override def preF(posInExpr : PosInExpr, f : Formula) = {
          if(posInExpr.equals(position.inExpr)) {
            formula = Some(f)
            Left(Some(ExpressionTraversal.stop))
          }
          else { Left(None) }
        }
      }
      ExpressionTraversal.traverse(fn, sequent(position))
      formula
    }
  }


  abstract class ApplyPositionTactic(name: String, val t: PositionTactic) extends Tactic("Position tactic " + name + "(" + t.name + ")") {
    def apply(tool: Tool, node: ProofNode) {
      findPosition(node) match {
        case Some(pos) => {
          val tactic = assertT(_ => t.applies(node.sequent, pos), "Position tactic is applicable at found position.") & t(pos)
          tactic.continuation = continuation
          tactic.dispatch(this, node)
        }
        case _ => continuation(this, Failed, Seq(node))
      }
    }

    def findPosition(pn: ProofNode): Option[Position] = findPosition(pn.sequent)
    def findPosition(s: Sequent): Option[Position]
  }

  /**
   * Allows construction of tactics based upon the proof node. Every axiom uses
   * the construction tactic.
   * 
   * If you choose a position based upon some information in the current sequent
   * (e.g. instantiating a quantifier), then you might construct a tactic based 
   * upon the proof nodes.
   */
  abstract class ConstructionTactic(name: String) extends Tactic("Construct " + name) {
    final def apply(tool: Tool, node: ProofNode) {
      constructTactic(tool, node) match {
        case Some(t) => {
          t.continuation = continuation
          t.dispatch(this, node)
        }
        case None => continuation(this, Failed, Seq(node))
      }
    }

    def constructTactic(tool: Tool, node: ProofNode): Option[Tactic]
  }

  /**
   * Base tactic that directly uses the given Provable.
   * Provable2Tactic conversion.
   * @see [[TactixLibrary.proveBy(Sequent,Tactic)]]
   */
  case class ByProvable(provable: Provable) extends Tactic("By provable " + provable) {

    def applicable(node : ProofNode): Boolean = node.sequent==provable.conclusion

    def apply(tool : Tool, node : ProofNode) {
      if (applicable(node)) {
        incRule()
        val res = measure(node(provable))
        // call updateInfo in order to propagate information along this proof node
        this.root match {
          case Some(r) =>
            r.updateStepInfo(res.tacticInfo)
            for(n <- res.subgoals) r.updateInfo(n.tacticInfo)
          case None =>
            this.updateStepInfo(res.tacticInfo)
            for(n <- res.subgoals) this.updateInfo(n.tacticInfo)
        }
        continuation(this, checkStats(Success), res.subgoals)
      } else {
        continuation(this, Failed,  Seq(node))
      }
    }

  }

  object LabelBranch {
    def apply(s: String): Tactic = new LabelBranch(s)
  }
  /**
   * Pseudo-tactic that has no effect but labeling the proof node
   * @see BranchLabels
   */
  class LabelBranch(s: String) extends Tactic("Label branch " + s) {
    override def applicable(node: ProofNode): Boolean = true

    override def apply(tool: Tool, node: ProofNode): Unit = {
      node.tacticInfo.infos += ("branchLabel" -> s)
      continuation(this, Success, Seq(node))
    }
  }

  object ProofNodeView {
    def apply(n: ProofNode): ProofNodeView = new ProofNodeView(n)
  }
  sealed class ProofNodeView(private val n: ProofNode) {
    def tacticInfo = n.tacticInfo
    def sequent = n.sequent
    def parent = ProofNodeView(n.parent)
    def children = n.children.map(ProofStepView.apply)

    override def toString: String = n.toString
  }

  object ProofStepView {
    def apply(n: ProofNode.ProofStep): ProofStepView = new ProofStepView(n)
  }
  //@todo document
  sealed class ProofStepView(private val s: ProofNode.ProofStep) {
    // TODO check when this is allowed to be readable
    def tacticInfo = s.tacticInfo
    //def rule = s.rule
    def goal = ProofNodeView(s.goal)
    def subgoals = s.subgoals.map(ProofNodeView.apply)

    override def toString: String = s.toString
  }

  /**
   * All user written tactics should be derived from UserTactic
   * @param name
   */
  abstract class UserTactic(name: String) extends ConstructionTactic("User " + name) {
    final def constructTactic(tool: Tool, node: ProofNode) = userTactic(tool, ProofNodeView(node))

    /**
     * This method should construct the user tactic. It only gets a view on the proof tree in order to make sure
     * that rules are only applied using the ApplyRule tactic (for bookkeeping purposes).
     *
     * @param tool
     * @param node
     * @return
     */
    def userTactic(tool: Tool, node: ProofNodeView): Option[Tactic]
  }

}
