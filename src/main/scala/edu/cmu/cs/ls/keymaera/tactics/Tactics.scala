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
import edu.cmu.cs.ls.keymaera.core.Config._
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
    // repeat tactic until a fixed point is reached
    def * : Tactic = repeatT(this)
    // apply the first tactic applicable
    def |(o: Tactic): Tactic = eitherT(this, o)
    // t1 ~ t2 = (t1 & t2) | t2
    def ~(o: Tactic): Tactic = weakSeqT(this, o)
    // execute this tactic and the given tactics on the resulting branches
    def &(o: Tactic*): Tactic = seqComposeT(this, o: _*)
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
    result.foreach(n => n.checkParentClosed())
  }

  /*
  def onSuccess(tNext : Tactic)(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    if (status == Success) result.foreach((n : ProofNode) => tNext.dispatch(tFrom, n))
  }
  */

  def onSuccess(tNext : Tactic*)(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    if (status == Success) {
      val len = math.max(tNext.length, result.length)
      def cont[A] = Stream.continually(_: Seq[A]).flatten.take(len).toList
      for ((t, n) <- cont(tNext) zip cont(result)) t.dispatch(tFrom, n)
    }
  }

  def onSuccessExact(tNext : Tactic*)(tFrom : Tactic, status : Status, result : Seq[ProofNode]) {
    if (status == Success) {
      if(tNext.length == result.length) {
        val len = math.max(tNext.length, result.length)
        def cont[A] = Stream.continually(_: Seq[A]).flatten.take(len).toList
        for ((t, n) <- cont(tNext) zip cont(result)) t.dispatch(tFrom, n)
      }
    }
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

  def seqComposeT(left: Tactic, rights: Tactic*) =
    new Tactic("SeqComposeT(" + left.name + ", " + rights.mkString(", ") + ")") {
      def applicable(node : ProofNode) = left.applicable(node)

      def apply(tool : Tool, node : ProofNode) = {
        if(rights.length > 0) {
          for (t <- rights)
            t.continuation = continuation
          left.continuation = onSuccess(rights: _*)
        } else {
          left.continuation = continuation
        }
        left.dispatch(this, node)
      }
    }

   def seqComposeExactT(left: Tactic, rights: Tactic*) =
    new Tactic("SeqComposeT(" + left.name + ", " + rights.mkString(", ") + ")") {
      def applicable(node : ProofNode) = left.applicable(node)

      def apply(tool : Tool, node : ProofNode) = {
        if(rights.length > 0) {
          for (t <- rights)
            t.continuation = continuation
          left.continuation = onSuccessExact(rights: _*)
        } else {
          left.continuation = continuation
        }
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

  def branchT(tcts: Tactic*): Tactic = new Tactic("branch") {
    def applicable(node: ProofNode) = true

    def apply(tool: Tool, node: ProofNode) = {
      for(t <- tcts) {
        t.continuation = continuation
        t.dispatch(this, node)
      }
    }
  }

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

  abstract class PositionTactic(val name: String) {
    def applies(s: Sequent, p: Position): Boolean

    def apply(p: Position): Tactic
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

}
