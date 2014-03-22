package edu.cmu.cs.ls.keymaera.tests

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.core.KeYmaera
import edu.cmu.cs.ls.keymaera.tactics._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

object SchedulerTests {

  val tool = Array(KeYmaera, KeYmaera, KeYmaera, KeYmaera)
  val scheduler = new Scheduler(tool)


  def test = {

    val a = new TacticsWrapper(new HuhuTactic("A"))
    val b = new TacticsWrapper(new HuhuTactic("B"))
    val c = new TacticsWrapper(new HuhuTactic("C"))
    val d = new TacticsWrapper(new HuhuTactic("D"))
    val e = new TacticsWrapper(new HuhuTactic("E"))
    val f = new TacticsWrapper(new HuhuTactic("F"))
    val g = new TacticsWrapper(new HuhuTactic("G"))
    val h = new TacticsWrapper(new HuhuTactic("H"))

    a.listener += new TacticsListener(a.tactic, (t : Tactic) => scheduler.dispatch(a))

    scheduler.dispatch(h)
    scheduler.dispatch(g)
    scheduler.dispatch(f)
    scheduler.dispatch(e)
    scheduler.dispatch(d)
    scheduler.dispatch(c)
    scheduler.dispatch(b)
    scheduler.dispatch(a)

  }

}
