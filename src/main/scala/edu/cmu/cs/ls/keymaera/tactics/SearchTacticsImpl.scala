package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._
import edu.cmu.cs.ls.keymaera.tactics.Tactics.{ConstructionTactic, ApplyPositionTactic, Tactic, PositionTactic}

/**
 * Implementation of search tactics.
 */
object SearchTacticsImpl {

  /**
   * Locates a position in the antecedent where the specified position tactic is applicable.
   * @param posT The position tactic.
   * @return A new tactic that applies said tactic at the specified position.
   */
  protected[tactics] def locateAnte(posT: PositionTactic): Tactic = new ApplyPositionTactic("locateAnte (" + posT.name + ")", posT) {
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
  protected[tactics] def locateSucc(posT: PositionTactic): Tactic = new ApplyPositionTactic("locateSucc (" + posT.name + ")", posT) {
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
  protected[tactics] def lastSucc(pt: PositionTactic): Tactic = new ConstructionTactic("Apply " + pt.name + " succ.length - 1") {
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
  protected[tactics] def lastAnte(pt: PositionTactic): Tactic = new ConstructionTactic("Apply " + pt.name + " ante.length - 1") {
    override def applicable(node: ProofNode): Boolean =
      pt.applies(node.sequent, AntePosition(node.sequent.ante.length - 1))

    override def constructTactic(tool: Tool, node: ProofNode): Option[Tactic] =
      Some(pt(SuccPosition(node.sequent.ante.length - 1)))
  }
}
