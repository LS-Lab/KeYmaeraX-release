import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.TacticLibrary._
import edu.cmu.cs.ls.keymaera.tactics.{TacticWrapper, Tactics, TacticLibrary}
import edu.cmu.cs.ls.keymaera.tactics.Tactics.Tactic

import scala.collection.immutable.Nil


def prove(f:Formula, tactic:Tactic = TacticLibrary.default, printOnFail: Boolean = true)  = {
  val r = new RootNode(new Sequent(Nil, Vector(), Vector(f)))
  Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, r))
  //For all schedulers, no one is working anymore.
  tactic.synchronized {
    tactic.registerCompletionEventListener(_ => tactic.synchronized(tactic.notifyAll))
    tactic.wait
  }
}

  val tactic = ((locate(indecisive(true, false, false, true)) | closeT)*)
  val A = PredicateConstant("A", None)
  val B =  PredicateConstant("B", None)
  val formula = Imply(A, Imply(B, A))
  prove(formula, tactic)

