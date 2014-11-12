package edu.cmu.cs.ls.keymaera.hydra

import edu.cmu.cs.ls.keymaera.core.{Tool, Mathematica, ProofNode}
import edu.cmu.cs.ls.keymaera.tactics.{TacticWrapper, Tactics, TacticLibrary}
import edu.cmu.cs.ls.keymaera.tactics.Tactics.Tactic


/**
 * TODO this should be deleted at some point, or else this should be refactored out of KeYmaeraInterface (probably the latter).
 * Created by nfulton on 11/11/14.
 */
object TacticInterface {
  val defaultTool = new Mathematica()
  val defaultTactic = TacticLibrary.default

  /**
   * This method is for debugging only! Please do not use in production!
   * @deprecated
   * @param node
   * @param tactic
   * @param tool
   * @return true iff node is closed.
   */
  def runSynchronizedTactic(node : ProofNode, tactic : Tactic = defaultTactic, tool : Tool = defaultTool) = {
    if(!tactic.applicable(node)) throw new Exception("Tried to apply a bad tactic!")

    tactic.apply(tool, node)
    Tactics.KeYmaeraScheduler.dispatch(new TacticWrapper(tactic, node))

    tactic.synchronized { tactic.registerCompletionEventListener(_ => tactic.synchronized(tactic.notifyAll)); tactic.wait() }
    node.isClosed()
  }

  /**
   * @todo Unlike runSyncrhonizedTactic, this method should instead update the database whenever the tactic notify's.
   * @param node
   * @param tactic
   * @param tool
   */
  def runTactic(db : DBAbstraction, node : ProofNode, tactic : Tactic, tool : Tool) : Unit = {
    ???
  }
}
