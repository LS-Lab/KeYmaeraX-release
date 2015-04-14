/**
 * Obsolete Proof Tree data structures
 * @author Jan-David Quesel
 * @author aplatzer
 * @author nfulton
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaera.tactics

// require favoring immutable Seqs for soundness

import edu.cmu.cs.ls.keymaera.core.{Provable, Rule, Sequent}

import scala.annotation.elidable
import scala.annotation.elidable._
import scala.collection.immutable.{List, Map}

  sealed abstract class Status
    case object Success       extends Status
    case object Failed        extends Status // counterexample found
    case object Unfinished    extends Status
    case object LimitExceeded extends Status
    case object Pruned        extends Status
    case object ParentClosed  extends Status

  /**
   * Proof Tree
   *============
   */

  /**
   * Additional proof node information payload for tactics.
   * @TODO Make branchLabels more general (and more typed) by allowing certain combinations of lables or modifiers to apply. Such as "cutShowLbl"&"invisible" for an invisible branch that proves a cut formula.
   */
  class ProofNodeInfo(var infos: Map[String, String], val proofNode: ProofNode) {
       //@TODO Role of closed and status is unclear. Who ever closes that? What does it have to do with the proof? It's just status information, not closed in the sense of proved. Maybe rename to done? Also possibly move into mixin trait as separate non-core feature?
    //@TODO Is this an invariant closed <=> status==Success || status==Failed || status==ParentClosed?
    @volatile private[this] var closed : Boolean = false
    @volatile var status               : Status  = Unfinished

    def isLocalClosed: Boolean = closed

    //@TODO Purpose and function unclear
    //@TODO rename to doneNode since it's not about closed in the sense of proved. Only closed in the sense of done with it even if disproved.
    def closeNode(s : Status) =
      this.synchronized {
        if (!closed) {
          closed = true
          status = s
          } else {
            assert (status == s, "status unchanged when closing already closed ProofNode with status " + status + " to " + s + " for " + this)
          }
      }

      //@TODO Purpose and function unclear
    def checkParentClosed() : Boolean = {
      var node = proofNode
      while (node != null && !node.tacticInfo.isLocalClosed) node = node.parent
      if (node == null) {
        return false
      } else {
        node = proofNode
        while (node != null && !node.tacticInfo.isLocalClosed) {
          node.tacticInfo.closeNode(ParentClosed)
          node = node.parent
        }
        return true
      }
    }
  }

  class ProofStepInfo(var infos: Map[String, String])

  @deprecated("Use Provable() instead.")
  object ProofNode {
    /**
     * Represents a deduction step in a proof using the indicated rule which leads to the given conjunctive list of subgoals.
     * Note that only ProofNode.apply is allowed to construct proof steps.
     * @param goal - parent of the step
     * @param subgoals - children of the step
     * @todo could merely use a Provable as evidence rather than remembering the Rule as evidence.
     */
    sealed case class ProofStep private[ProofNode] (rule : Rule, goal : ProofNode, subgoals : scala.collection.immutable.List[ProofNode], tacticInfo: ProofStepInfo = new ProofStepInfo(Map())) {
      justifiedByProofRule
      @elidable(ASSERTION) def justifiedByProofRule = {
//        println("Checking " + this)
//        println("Reapply  " + rule(goal.sequent))
        require(rule(goal.sequent) == subgoals.map(_.sequent), this + "\nled to subgoals\n" + rule(goal.sequent))
//        println("Checked  " + this)
      }

      override def toString() = "ProofStep(" + rule + "\napplied to goal\n\n" + goal + "\n\nexpects subgoals\n" + subgoals.map(_.sequent).mkString(",\n") + ")"
    }
  }

  sealed class ProofNode protected (val parent : ProofNode, val provable: Provable, val subgoal: Int) {
    /**
     * Whether to keep full provables or just local provables around as evidence.
     */
    private val fullProvable = false

    @volatile private[this] var alternatives : List[ProofNode.ProofStep] = Nil


    /**
     * Soundness-critical invariant that all alternative proof steps have us as their goal.
     * Dropping alternatives is sound, but adding alternatives requires passing this invariant.
     */
    @elidable(ASSERTION) private def checkInvariant =
      assert(alternatives.forall(_.goal == this), "all alternatives are children of this goal")

    def sequent : Sequent = provable.subgoals(subgoal)

    /**
     * List of all current or-branching alternatives of proving this proof node.
     * Result can change over time as new alternative or-branches are added.
     */
    def children: scala.collection.immutable.List[ProofNode.ProofStep] = {
      checkInvariant
      alternatives
    }

    def hasAlternative : Boolean = alternatives != Nil
    def nextAlternative : ProofNode.ProofStep = {
      require(hasAlternative, "apply proof rule before calling nextAlternative")
      alternatives match {
        case List(h, t) => h
        case Nil        => throw new IllegalArgumentException("getStep can only be invoked when there is at least one alternative.")
      //@TODO change exception type to a prover exception.
      }
    }

    def pruneAlternative(n : Int) {
      this.synchronized {
        if (n < alternatives.length)
          alternatives = alternatives.take(n-1) ++ alternatives.drop(n)
        else
          throw new IllegalArgumentException("Pruning an alternative from a proof tree requires this alternative to exists.")
      }
    }

    /**
     * Apply the given proof rule to this ProofNode.
     * Return the resulting list of subgoals (after including them as an or-branch alternative for proving this ProofNode).
     * Soundness-critical proof rule application mechanism.
     */
    final def apply(rule : Rule) : ProofNode.ProofStep = {
      // ProofNodes for the respective sequents resulting from applying rule to sequent.
      checkInvariant
      val proofStep = {
        if (fullProvable) { // keep full provable around
          val newProvable = provable(rule, subgoal)
          val subgoals = if (newProvable.subgoals.length < provable.subgoals.length) List()
          else List(new ProofNode(this, newProvable, subgoal)) ++
            Range(provable.subgoals.length, newProvable.subgoals.length).
              map(new ProofNode(this, newProvable, _))
          //@TODO assert(all subgoals have the same provable and the same parent)
          ProofNode.ProofStep(rule, this, subgoals)
        } else {  // only keep subProvable around to simplify subsequent merge
          val newProvable = provable.sub(subgoal)(rule, 0)
          ProofNode.ProofStep(rule, this, Range(0, newProvable.subgoals.length).
            map(new ProofNode(this, newProvable, _)).toList)
        }
      }
      // Add as or-branching alternative
      this.synchronized {
        alternatives = alternatives :+ proofStep
      }
      checkInvariant
      proofStep
    }

    // TODO: there should be a TestCase that checks that this field is never read in the prover core
    val tacticInfo: ProofNodeInfo = new ProofNodeInfo(if(parent == null) Map() else parent.tacticInfo.infos, this)

    override def toString = "ProofNode(" + sequent + " by " +
      (if (parent != null) parent.tacticInfo.infos.get("Executing tactic")
       else "") +
      "\nfrom " + parent + ")"

    /**
     * @return true iff the node is marked as closed by proof node management, which is not necessarily correct.
     * The sound way of checking whether a proof finished successfully is asking isProved()
     * @see #isProved()
     */
    def isClosed(): Boolean =
      children.map((f: ProofNode.ProofStep) =>  f.subgoals.foldLeft(true)(_ && _.isClosed())).contains(true)

    /**
     * Test whether this ProofNode can be proved by merging Provable's of one of its alternatives.
     * @TODO The sound version needs to find an alternative
     *      that it can successively merge via Provability.apply(Provable, Int) to yield an isProved()
     * @TODO Could return Provable witness too.
     */
    def isProved(): Boolean = ???

    /**
     * Retrieves a list of open goals.
     * @return the list of all childless proof nodes in a proof tree.
     */
    def openGoals() : List[ProofNode] = {
      children match {
        case Nil => if(isClosed()) Nil else this :: Nil
        case _   => children.flatMap(_.subgoals.flatMap(_.openGoals()))
      }
    }
  }

  /**
   * The root node (conclusion) where a sequent derivation starts.
   */
  class RootNode(sequent : Sequent) extends ProofNode(null, Provable.startProof(sequent), 0) {

  }
