/**
 * Thread pool and scheduler for tactics
 * =====================================
 *
 * (For simplicity use java threads)
 
 * Instantiate scheduler instance for each tool with the number of
 * threads equalling the amount of parallelism that the tool provides,
 * for example, the number of licenses or the number of available
 * cores.
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
 * 2) 
 */

package edu.cmu.cs.ls.keymaera.tactics

//import edu.cmu.cs.ls.keymaera.tactics.TacticsWrapper
//import edu.cmu.cs.ls.keymaera.tactics.TacticsListener
import edu.cmu.cs.ls.keymaera.core.Tool

import scala.Array
import java.lang.Runnable
import scala.collection.mutable.SynchronizedPriorityQueue
import scala.annotation.elidable
import scala.annotation.elidable._

import java.lang.InterruptedException
import java.util.NoSuchElementException

class StopInterruptedException extends InterruptedException {}

/**
 * The thread that traverses the prioList to find and execute tactics
 */
class TacticsExecutor[T <: Tool](val scheduler : Scheduler[T], val id : Int, val tool : Tool) extends java.lang.Runnable {

  override def run() {
    println ("I think I am " + id + " therefor I am: " + this)

    var runnable : Boolean = true

    while (runnable) {
      /* pick tactic; execute apply; wait for interrupts , ... */
      try {
        try {
          scheduler.prioList.dequeue().apply(tool)
        } catch {
          case ex : NoSuchElementException => {
/*            println("list is empty")*/
            /* poll */
          }
        }
      } catch {
        case ex : StopInterruptedException => {
          tool.shutdown()
          runnable = false
        }
        case ex : InterruptedException => {
          tool.check_and_recover()
        }
      }
    }
  }

}

/**
 * Main scheduler class; contains prio list and starts scheduler threads upon creation
 */
class Scheduler[T <: Tool](tools : Array[T]) {

  val maxThreads = tools.size
  var thread : Array[java.lang.Thread] = new Array(maxThreads)
  var prioList : SynchronizedPriorityQueue[TacticsWrapper] = new SynchronizedPriorityQueue()


  for (x <- 0 to maxThreads - 1) {
    thread.update(x, new java.lang.Thread(new TacticsExecutor(this, x, tools(x))))
  }

  thread.foreach(_.start())

  def dispatch(t : TacticsWrapper) = prioList += t

}


