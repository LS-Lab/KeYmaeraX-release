package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics._

/**
 * Implementation of search tactics.
 */
object SearchTacticsImpl {

  /**
   * Locates a position in the antecedent where the specified position tactic is applicable.
   * @param posT The position tactic.
   * @return A new tactic that applies said tactic at the specified position.
   */
  def locateAnte(posT: PositionTactic): Tactic = new ApplyPositionTactic("locateAnte (" + posT.name + ")", posT) {
    override def applicable(p: ProofNode): Boolean = findPosition(p.sequent).isDefined

    override def findPosition(s: Sequent): Option[Position] = {
      for (i <- 0 until s.ante.length) {
        val pos = AntePosition(i)
        if(posT.applies(s, pos)) {
          return Some(pos)
        }
      }
      None
    }
  }

  /**
   * Locates a position in the succedent where the specified position tactic is applicable.
   * @param posT The position tactic.
   * @return A new tactic that applies said tactic at the specified position.
   */
  def locateSucc(posT: PositionTactic): Tactic = new ApplyPositionTactic("locateSucc (" + posT.name + ")", posT) {
    override def applicable(p: ProofNode): Boolean = findPosition(p.sequent).isDefined

    override def findPosition(s: Sequent): Option[Position] = {
      for (i <- 0 until s.succ.length) {
        val pos = SuccPosition(i)
        if(posT.applies(s, pos)) {
          return Some(pos)
        }
      }
      None
    }
  }

  /**
   * Applies a position tactic at the last position in the succedent.
   * @param pt The position tactic.
   * @return The new tactic to apply said position tactic at the last position.
   */
  def lastSucc(pt: PositionTactic): Tactic = new ConstructionTactic("Apply " + pt.name + " succ.length - 1") {
    override def applicable(node: ProofNode): Boolean =
      pt.applies(node.sequent, SuccPosition(node.sequent.succ.length - 1))

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
      Some(pt(SuccPosition(node.sequent.succ.length - 1)))
  }

  /**
   * Applies a position tactic at the last position in the antecedent.
   * @param pt The position tactic.
   * @return The new tactic to apply said position tactic at the last position.
   */
  def lastAnte(pt: PositionTactic): Tactic = new ConstructionTactic("Apply " + pt.name + " ante.length - 1") {
    override def applicable(node: ProofNode): Boolean =
      pt.applies(node.sequent, AntePosition(node.sequent.ante.length - 1))

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
      Some(pt(SuccPosition(node.sequent.ante.length - 1)))
  }

  /**
   * Creates a new tactic, which applies a tactic on the branch identified with the specified branch label, if such
   * branch exists.
   * @param s The branch label.
   * @param t The tactic to apply on said branch.
   * @return The new tactic.
   */
  def onBranch(s: String, t: Tactic): Tactic = ifT(_.tacticInfo.infos.get("branchLabel") == Some(s), t)

  /**
   * used to say "do equiv-r". On the left branch of that, do my
   * branch1 tactic and on the right brance I want to follow branch2 as a tactic.
   *
   * onBranch is used when you have a very specific tactic you only want to run
   * on a branch where you know it will work. e.g. "I know that tacticX will work
   * on the left side because it's exactly what we need, but tacticX is not useful
   * anywhere else."
   *
   * This could be useful for macro recording so that we can provide a concise
   * proof script of what we did. That way this can be used on another proof where
   * the exact proof steps might not be necessary but the tactic might be very
   * useful.
   *
   * Idea: tie together the interface that we had in KeYmaera with tactic writing
   * (I have an idea what my proof will look like
   */
  def onBranch(s1: (String, Tactic), spec: (String, Tactic)*): Tactic =
    if(spec.isEmpty)
      ifT(_.tacticInfo.infos.get("branchLabel") == Some(s1._1), s1._2)
    else
      switchT((pn: ProofNode) => {
        pn.tacticInfo.infos.get("branchLabel") match {
          case None => NilT
          case Some(l) =>
            val candidates = (s1 +: spec).filter((s: (String, Tactic)) => l == s._1)
            if(candidates.isEmpty) NilT
            else {
              require(candidates.length == 1, "There should be a unique branch with label " + l
                + " however there are " + candidates.length + " containing " + candidates.map(_._1))
              candidates.head._2
            }
        }
      })
}
