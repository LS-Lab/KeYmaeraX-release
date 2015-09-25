/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
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

package edu.cmu.cs.ls.keymaerax.tactics

import Config._
import edu.cmu.cs.ls.keymaerax.tactics.Tactics._
import java.util.NoSuchElementException

import edu.cmu.cs.ls.keymaerax.tools.Tool

/**
 * Binds a tactic for execution to a specific tool.
 */
trait TacticToolBinding extends Ordered[TacticToolBinding] {
  /**
   * Executes the tactic on the specified tool/
   * @param tool The tool to execute the tactic.
   */
  def execute(tool: Tool)

  /**
   * The tactic to execute.
   * @return The tactic.
   */
  def tactic: Tactic
}

/** Interface for classes that want to know about tactic exceptions */
trait TacticExceptionListener {
  /**
   *
   * @param tactic The tactic that threw the exception.
   * @param exn The exception that was thrown.
   */
  def acceptTacticException(tactic: Tactic, exn : Exception) : Unit
}

/**
 * Executes a tactic on a tool.
 */
class TacticWrapper(val tactic : Tactic, val node : ProofNode) extends TacticToolBinding {
  var listeners : List[TacticExceptionListener] = List()
  def addListener(listener : TacticExceptionListener) : Unit =
    listeners = listeners :+ listener
  def removeListener(listener : TacticExceptionListener) : Unit =
    listeners = listeners.filter(l => !l.equals(listener))

  def compare(that : TacticToolBinding) = this.tactic.priority - that.tactic.priority

  def execute(tool : Tool) = {
    tactic.incTacs()
    if (tactic.tacs > tacThres) {
      tactic.tacs = 0
      node.tacticInfo.checkParentClosed()
    }
    if (!node.tacticInfo.isLocalClosed) {
      try {
        if (tactic.applicable(node)) {
          node.tacticInfo.infos += "Executing tactic" -> tactic.toString
          tactic(tool, node)
        } else {
          tactic.continuation(tactic, Failed, Seq(node))
        }
      } catch {
        case e: Exception => {
          listeners.foreach(l => l.acceptTacticException(tactic, e))
          e.printStackTrace()
          tactic.continuation(tactic, Failed, Seq(node))
        }
      }
    }
    tactic.unregister
  }

}

class TacticExecutor(val scheduler : Scheduler, val tool : Tool, val id : Int) extends java.lang.Runnable {

  @volatile private var stopped: Boolean = false

  override def run() {
    @volatile var runnable: Boolean = true

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
          case ex: NoSuchElementException => scheduler.synchronized {
            // TODO swallows useful exceptions, implement waiting for real
            /* poll vs. wait */
            scheduler.blocked = scheduler.blocked + 1
            scheduler.wait()
          }
        }
      } catch {
        case ex: InterruptedException =>
          if (stopped) {
            tool.shutdown()
            runnable = false
          } else {
            tool.restart()
          }
      }
    }
  }

  def stop(): Unit = {
    stopped = true
  }

}

/**
 * Executes tactics on tools.
 */
trait ExecutionEngine {
  /** Initializes the execution engine with configuration values specified as key-value pairs */
  def init(config: Map[String,String]): Unit
  /** Indicates whether or not the execution engine is initialized */
  def isInitialized: Boolean
  /** Shuts down the execution engine */
  def shutdown(): Unit
  /** Executes the specified tactic */
  def dispatch(t: TacticToolBinding): ExecutionEngine
}

/**
 * Main scheduler class; contains prio list and starts scheduler threads upon creation
 */
class Scheduler(tools : Seq[Tool]) extends ExecutionEngine {

  val maxThreads = tools.length
  val thread   : Array[java.lang.Thread] = new Array(maxThreads)
  val executors: Array[TacticExecutor] = new Array(maxThreads)
  val prioList = new scala.collection.mutable.SynchronizedPriorityQueue[TacticToolBinding]()
  var initialized = false
  @volatile var blocked = 0/* threads blocked on the scheduler */

  override def init(config: Map[String,String]) = {
    for (x <- 0 to maxThreads - 1) {
      val te = new TacticExecutor(this, tools(x), x)
      executors.update(x, te)
      thread.update(x, new java.lang.Thread(te))
    }
    blocked = 0
    tools.foreach(_.init(config))
    thread.foreach(_.start())
    initialized = tools.exists(_.isInitialized)
  }

  override def isInitialized: Boolean = initialized

  override def shutdown() = {
    executors.foreach(_.stop())
    // interrupt long running tools to make them check their stopped flag
    thread.foreach(_.interrupt())
    // wait for the threads run to completion
    thread.foreach(_.join())
  }

  override def dispatch(t : TacticToolBinding) = {
    prioList += t
    this.synchronized {
      if (blocked > 0) {
        blocked = blocked - 1
        notify() /* release one executor at a time to avoid trampling herd */
      }
    }
    this
  }
}

/**
 * Sequential interpretation of tactics.
 * @param tool The tool to execute tactics.
 */
class Interpreter(tool : Tool) extends ExecutionEngine {
  private var initialized = false
  override def init(config: Map[String,String]) = {
    tool.init(config)
    initialized = tool.isInitialized
  }

  override def isInitialized: Boolean = initialized

  override def shutdown() = tool.shutdown()

  override def dispatch(t : TacticToolBinding) = {
    t.execute(tool)
    this
  }
}



