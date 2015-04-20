package edu.cmu.cs.ls.keymaera.tests

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.core.KeYmaera
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tactics.{RootNode, ProofNode, Scheduler}
import scala.collection.immutable

object SchedulerTests {

  val sched = new Scheduler(Seq(KeYmaera, KeYmaera, KeYmaera))

  def huhu(id : String) = new Tactic("Huhu " + id) {
    scheduler = sched
    def applicable(node : ProofNode) : Boolean = true
    def apply  (tool : Tool, node : ProofNode) {
//      println (name + " got applied")
      incRule()
    }
  }

  def test() {
    val r = new RootNode(new Sequent(immutable.IndexedSeq.empty, immutable.IndexedSeq.empty, immutable.IndexedSeq.empty))

    val a = huhu("a")
    val b = huhu("b")
    val c = huhu("c")
    val d = huhu("d")
    val e = huhu("e")
    val f = huhu("f")
    val g = huhu("g")
    val h = huhu("h")

  }

}
