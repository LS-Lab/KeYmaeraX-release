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

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.core.Tool
import Config._
import scala.Unit
import scala.language.implicitConversions

/**
 * @author jdq
 *
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

  val KeYmaeraScheduler = new Scheduler(Seq.fill(Config.maxCPUs)(KeYmaera))
  val MathematicaScheduler = new Scheduler(for (i <- 0 until Config.mathlicenses) yield new Mathematica)



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
        // FIXME: what was the intention of this loop? It's an infinite loop like this (therefore commented out for now)
        /*while (p != null)*/ r = p.update(s) || r
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

  type Continuation = (Tactic, Status, Seq[ProofNode]) => Unit

  abstract class Tactic(val name : String) extends Stats {

    var scheduler : Scheduler = KeYmaeraScheduler

    var limit  : Limits = defaultLimits

    var continuation : Continuation = stop

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

    /**
     * The root tactic is passed on via dispatches.
     */
    var root : Tactic = null

    def unregister(t : Tactic) {
      if(root != null) {
        root.unregister(t)
      }
      else {
        System.err.println("I am the root -- todo")
        //TODO here we modify some data structure.
      }
    }
    
    //@TODO -- registration.
    def registerRunningTactic(t : Tactic) : Unit = {
      if(root != null) {
        root.registerRunningTactic(t)
      }
      else {
        System.err.println("I am the root -- todo")
        //TODO here we modify some data structure.
      }
    }
    
    /**
     * Called whenever a new tactic is dispatched.
     * @param t - parent tactic
     */
    def dispatch(t : Tactic, l : Limits, node : ProofNode) {
      inheritStats(t)
      limit = l
      scheduler.dispatch(new TacticWrapper(this, node))
      this.root = t.root
      registerRunningTactic(this)
    }

    def dispatch(t : Tactic, node : ProofNode) { dispatch(t, t.limit, node) }

    def checkStats(res : Status) : Status = limit.checkStats(this)(res)

    /**
     * Convenience wrappers
     */
    // repeat tactic until a fixed point is reached
    def * : Tactic = repeatT(this)
    // apply the first tactic applicable
    def |(o: Tactic): Tactic = eitherT(this, o)
    // t1 ~ t2 = (t1 & t2) | t2
    def ~(o: Tactic): Tactic = weakSeqT(this, o)
    // execute this tactic and the given tactics on the resulting branches
    def &(a: Tactic, o: Tactic*): Tactic = seqComposeT(this, a, o: _*)
    def &&(a: Tactic, o: Tactic*): Tactic = seqComposeExactT(this, a, o: _*)
    // create an or-branch for each given tactic
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

  def stop(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    tFrom.limit.propagate(tFrom)
    result.foreach(n => n.info.checkParentClosed())
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
      if(tNext.length == result.length) {
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
        t.continuation = onChangeAndOnNoChange(node, onChange(node, this), continuation)
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
   * Apply rule
   */
  abstract class ApplyRule(val rule : Rule) extends Tactic("Apply rule " + rule) {

    def apply(tool : Tool, node : ProofNode) {
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
   * Takes a position tactic and ???
   */
  abstract class PositionTactic(val name: String) {
    def applies(s: Sequent, p: Position): Boolean

    def apply(p: Position): Tactic

    def &(pt: PositionTactic) = new PositionTactic("Seq(" + this.name + ", " + pt.name) {
      override def applies(s: Sequent, p: Position): Boolean = this.applies(s, p)

      // this crucially relies on stable positions
      override def apply(p: Position): Tactic = this.apply(p) & pt.apply(p)
    }
  }

  abstract class ApplyPositionTactic(name: String, val t: PositionTactic) extends Tactic("Position tactic " + name + "(" + t.name + ")") {
    def apply(tool: Tool, node: ProofNode) {
      findPosition(node) match {
        case Some(pos) => {
          val tactic = t(pos)
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

  object LabelBranch {
    def apply(s: String): Tactic = new LabelBranch(s)
  }
  class LabelBranch(s: String) extends Tactic("Label branch " + s) {
    override def applicable(node: ProofNode): Boolean = true

    override def apply(tool: Tool, node: ProofNode): Unit = {
      node.info.branchLabel = s
      continuation(this, Success, Seq(node))
    }
  }

}
