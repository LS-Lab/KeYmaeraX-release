/**
 * @author Marcus Völp
 */

package edu.cmu.cs.ls.keymaera.tactics


import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.core.Tool
import scala.Unit
import scala.math.Ordered
import scala.collection.mutable.SynchronizedQueue



/**
 * Framework for constructing and parallelizing tactics
 *
 * 1) Functions should dispatch a new tactic to the corresponding scheduler when invoking an external tool.
 */



/* ??? Interrupt Tactic ??? */



/**
 * The atomic operation that is to be executed
 * - captures state and result of applying a tactic on a proof node
 * - a scheduler thread will block while executing a function
 */
class TacticsWrapper(val tactic : Tactic) extends Ordered[TacticsWrapper] {

  var listener : SynchronizedQueue[TacticsListener] = new SynchronizedQueue()

  var priority : Int = 0
  def compare(that : TacticsWrapper) = this.priority - that.priority

  /* execute this tactic */
  def apply(tool : Tool) {
    tactic.apply(tool)
    listener.foreach(_.apply())
  }
}

/**
 * code that determines how to react on completion (successful or not)
 */
class TacticsListener(val tactic : Tactic, val fn : Tactic => Unit) {

  def apply() {
    println ("Invoking listener " + this + " on tactic " + tactic)
    fn(tactic)
  }

}

