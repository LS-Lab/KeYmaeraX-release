/**
 * Thread pool and scheduler for tactics
 * =====================================
 *
 * (For simplicity use java threads)
 
 * Instantiate scheduler instance for each tool with the number of
 * threads equalling the amount of parallelism that the tool provides,
 * for example, the number of licenses or the number of available
 * cores.
 *
 */


/**
 * Notes
 * =====
 *
 * Adding additional listeners to a dispatched tactic is racy avoid at all costs.
 */


/**
 * The Java / Scala sucks for parallel execution docu
 * ==================================================
 *
 * 1) CPU Affinity
 * ---------------
 *  Neither Java nor Scala supports CPU affinities, that is limiting
 *  a thread to a specific processor. There are some libraries for
 *  Linux but no generic support. This means we can run into
 *  situations where all SchedulerThreads run on the same core. The
 *  OS load balancer should take care about distributing them once
 *  the load they execute go up. It may be possible to pin external
 *  processes to CPUs.
 *
 * 2) foreach discouraged
 * ----------------------
 *  Although Java supports preemption points, foreach and other
 *  iterators do not. We therefore have to rely on manual iterators.
 */

package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core.{Failed, Tool, ProofNode}
import Config._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

import scala.Array
import java.lang.Runnable
import scala.collection.mutable.SynchronizedPriorityQueue
import scala.annotation.elidable
import scala.annotation.elidable._

import java.lang.InterruptedException
import java.util.NoSuchElementException

/**
 * The thread that traverses the prioList to find and execute tactics
 */
class TacticWrapper(val tactic : Tactic, val node : ProofNode) extends Ordered[TacticWrapper] {

  def compare(that : TacticWrapper) = this.tactic.priority - that.tactic.priority

  def execute(tool : Tool) = {
    tactic.incTacs()
    if (tactic.tacs > tacThres) {
      tactic.tacs = 0
      node.tacticInfo.checkParentClosed
    }
    if (!node.tacticInfo.isLocalClosed) {
      try {
        if (tactic.applicable(node))
          tactic(tool, node)
        else
          tactic.continuation(tactic, Failed, Seq(node))
      } catch {
        case e: Exception =>
          // TODO report exception somewhere useful
          e.printStackTrace()
          tactic.continuation(tactic, Failed, Seq(node))
      }
    }
    tactic.unregister
  }

}

class TacticExecutor(val scheduler : Scheduler, val tool : Tool, val id : Int) extends java.lang.Runnable {

  override def run() {
    @volatile var runnable : Boolean = true
    @volatile var stop     : Boolean = false

    while (runnable) {
      /* pick tactic; execute apply; wait for interrupts , ... */
      try {
        try {
          val t = scheduler.prioList.dequeue()
          t.execute(tool)
          if (Thread.interrupted) {
            throw new InterruptedException()
          }
        } catch {
          case ex : NoSuchElementException => {
            // TODO swallows useful exceptions, implement waiting for real
            /* poll vs. wait */
            scheduler.synchronized {
              scheduler.blocked = scheduler.blocked + 1
              scheduler.wait()
            }
          }
        }
      } catch {
        case ex : InterruptedException => {
          if (stop) {
            tool.shutdown()
            runnable = false
          } else {
            tool.check_and_recover()
          }
        }
      }
    }
  }

}

/**
 * Main scheduler class; contains prio list and starts scheduler threads upon creation
 */
class Scheduler(tools : Seq[Tool]) {

  val maxThreads = tools.length
  val thread   : Array[java.lang.Thread] = new Array(maxThreads)
  val prioList : SynchronizedPriorityQueue[TacticWrapper] = new SynchronizedPriorityQueue()
  @volatile var blocked  : Int = 0/* threads blocked on the scheduler */

  for (x <- 0 to maxThreads - 1)
    thread.update(x, new java.lang.Thread(new TacticExecutor(this, tools(x), x)))

  thread.foreach(_.start())

  def init(config: Map[String,String]) = tools.foreach(_.init(config))
  def shutdown() = tools.foreach(_.shutdown())

  def dispatch(t : TacticWrapper) : this.type = {
    prioList += t
    this.synchronized {
      if (blocked > 0) {
        blocked = blocked - 1
        notify() /* release one executor at a time to avoid trambling herd */
      }
    }
    return this
  }
}



