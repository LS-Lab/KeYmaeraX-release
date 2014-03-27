package edu.cmu.cs.ls.keymaera.tests

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.core.KeYmaera
import edu.cmu.cs.ls.keymaera.tactics.Tactics._
import edu.cmu.cs.ls.keymaera.tactics.Scheduler

object SchedulerTests {

  val sched = new Scheduler(Seq(KeYmaera, KeYmaera, KeYmaera))

  class Huhu(val id : String) extends Tactic("Huhu " + id, 
      new RootNode(new Sequent(IndexedSeq.empty, IndexedSeq.empty, IndexedSeq.empty))) {
    scheduler = sched
    def applies(tool : Tool) : Boolean = true
    def apply  (tool : Tool) = {
//      println (name + " got applied")
    }
  }

  def test = {
    val a = new Huhu("a")
    val b = new Huhu("b")
    val c = new Huhu("c")
    val d = new Huhu("d")
    val e = new Huhu("e")
    val f = new Huhu("f")
    val g = new Huhu("g")
    val h = new Huhu("h")

    val l = (x : Tactic) => new TacticsListener(x, (s, t) => {
      println ("applying and redispatching " + t)
      s ++ x
    })

    a.listeners += l(a)
    b.listeners += l(b)
    c.listeners += l(c)
    d.listeners += l(d)
    e.listeners += l(e)
    f.listeners += l(f)
    g.listeners += l(g)

    h.listeners += new TacticsListener(h, (s, t) => {
       println ("interrupting")
       scheduler.thread(0).interrupt
       scheduler.thread(1).interrupt
       scheduler.thread(2).interrupt
       s ++ h
    })

    scheduler ++ a ++ b ++ c ++ d ++ e ++ f ++ g ++ h
  }

}
