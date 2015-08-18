/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Obsolete Proof Tree data structures
 * @author Jan-David Quesel
 * @author Andre Platzer
 * @author nfulton
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaerax.tactics

// require favoring immutable Seqs for soundness

import edu.cmu.cs.ls.keymaerax.core.{CoreException, Provable, Rule, Sequent}

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

/** Tactic management information about a proof step, with mutable information state in blackboard style */
class ProofStepInfo(var infos: Map[String, String])

  object ProofNode {
    /**
     * Represents a deduction step in a proof using the indicated rule
     * which leads to the given conjunctive list of subgoals.
     * For soundness, only ProofNode.apply is allowed to construct proof steps.
     * But Provable is justifying soundness even without that constraint.
     * @param provable the Provable that is provable by using the given rule on the given goal yielding the given subgoals.
     * @param step the proof rule or Provable used in this proof step.
     * @param goal the goal that this ProofStep was applied to, i.e. its immediate conclusion.
     * @param subgoals subgoals resulting from using the given rule on the given goal.
     * @note could merely use a Provable as evidence rather than also remembering the Rule as evidence,
     *       but remembering the rule makes it easier to reconstruct.
     * @note Only private constructor calls to help soundness
     * @author Andre Platzer
     */
    //@deprecated("Redundant soundness-checking. Can use Provable() instead.")
    sealed case class ProofStep private[ProofNode] (provable: Provable,
                                                    step : Either[Rule,Provable],
                                                    goal : ProofNode,
                                                    subgoals : scala.collection.immutable.List[ProofNode],
                                                    tacticInfo: ProofStepInfo = new ProofStepInfo(Map())) {
      fitsToProvable
      @elidable(ASSERTION) def fitsToProvable = {
        require(conclusion == provable.conclusion, "ProofStep constructed with goal according to provable's conclusion")
        require(premises == provable.subgoals, "ProofStep constructed with subgoals according to provable's premises")
      }
      ruleJustifiesProvable
      @elidable(ASSERTION) def ruleJustifiesProvable = {
        assert(step.isRight || Provable.startProof(provable.conclusion)(rule, 0) == provable, "The ProofStep's rule is the witness for its provable")
      }
      //justifiedByProofRule //@note redundant re-check of ruleJustifiesProvable
      @elidable(ASSERTION) def justifiedByProofRule = {
//        println("Checking " + this)
//        println("Reapply  " + rule(goal.sequent))
        require(step.isRight || rule(conclusion) == premises, this + "\nled to subgoals\n" + rule(conclusion))
//        println("Checked  " + this)
      }

      /** The conclusion that this ProofStep proves from the premises, i.e., sequent of the goal */
      def conclusion = goal.sequent
      /** The premises that this ProofStep still needs to prove, i.e., sequents of the subgoals */
      def premises = subgoals.map(_.sequent)

      /** Whether this ProofStep uses a Rule (true) or merges a subderivation (false) */
      def isRule: Boolean = step.isLeft
      /** The rule used for this ProofStep if isRule */
      def rule: Rule = {require(isRule, "rule only makes sense if not subderivation"); step.left.get}
      /** The subderivation used for this ProofStep if !isRule */
      def subderivation: Provable = {require(!isRule); step.right.get}

      /** Whether this ProofStep has been closed, i.e., ran out of subgoals */
      private[ProofNode] def isClosed : Boolean = subgoals.foldLeft(true)(_ && _.isClosed())

      override def toString() = "ProofStep(" + (step match {
        case Left(rule) => rule.toString
        case Right(useProvable) => useProvable.toString
      }) + "\napplied to goal\n\n" + conclusion + "\n\nexpects subgoals\n" + premises.mkString(",\n") + ")"
    }
  }

/**
 * Proof Search Data Structure for tactics.
 * A proof node for the tactics trying to prove the given subgoal of Provable.
 * ProofNode(parent, provable, subgoal) sets out to prove the given subgoal of provable for the parent proof node.
 * Once that proof finished, the final proof certificate obtained after proof search can be extracted via [[provableWitness]].
 * @param parent The parent's proof node that this ProofNode is trying to help finish a full proof for.
 * @param provable The Provable that this ProofNode is trying to help prove by closing the given subgoal.
 * @param subgoal The subgoal of provable that this ProofNode is trying to prove.
 */
sealed class ProofNode protected (val parent : ProofNode, val provable: Provable, val subgoal: Int) {
  private val DEBUG = System.getProperty("DEBUG", "false")=="true"

  /**
   * Generate a Provable proof certificate corresponding to this proof search data structure.
   * If isClosed, the resulting Provable should be isProved
   * Finds an alternative that it can successively merge via
   * Provability.apply(Provable, Int) to yield a Provable that will be isProved().
   * @note generalization to !isClosed needs to be tested more if there's multiple open branches or alternatives.
   * @author Andre Platzer
   */
  final def provableWitness : Provable = {
    // probably not proved if isClosed status is not even set (may be conservatively incorrect)
    //require(isClosed, "Only ProofNodes that closed have a proved Provable " + this)
    if (children.isEmpty) {assert(!isClosed()); return provable}
    if (fullProvable) throw new UnsupportedOperationException("Not implemented if fullProvable=false")
    //@elidable assert(!provable.isProved && IndexedSeq(provable.conclusion) == provable.subgoals, "!fullProvable gives trivial identity Provables only\n" + provable + "\nfor " + this)
    // find any closed or-branch alternative
    val orStep: ProofNode.ProofStep = children.find(_.isClosed) match {
      case Some(step) => step
      //@note The following choice is arbitrary and could minimize the number of open goals as well.
      case None => assert(!children.isEmpty); children.head
      //  assert(false, "isClosed() should imply that there is at least one alternative ProofStep that is closed"); ???
    }
    assert(!DEBUG || orStep.conclusion == sequent && orStep.goal.sequent == sequent, "The alternative's ProofStep\n" + orStep + " fits to this ProofNode\n" + this)
    assert(!DEBUG || orStep.goal == this, "Goal of the alternative or-branch ProofStep is this")
    if (orStep.subgoals.isEmpty) {
      // apply the closing rule
      val done = if (orStep.isRule) provable(orStep.rule, subgoal) else provable(orStep.subderivation, subgoal)
      //@elidable assert(!isClosed || done.isProved, "ProofNodes with a ProofStep without subgoals are provable directly")
      done
    } else {
      // successively merge Provables of all subgoals
      var merged = if (orStep.isRule) provable(orStep.rule, subgoal) else provable(orStep.subderivation, subgoal)
      for (i <- orStep.subgoals.length to 1 by -1) {
        //@elidable assert(!isClosed || orStep.subgoals(i - 1).provableWitness.isProved, "isClosed() should imply that there is a closed Provable")
        merged = merged(orStep.subgoals(i - 1).provableWitness, i - 1)
      }
      //assert(merged.conclusion == provable.conclusion, "unchanged conclusion")
      //@elidable assert(!isClosed || merged.isProved, "isClosed() should imply that merging gives a closed Provable\n\n" + merged + "\n\nfor\n\n" + this)
      merged
    }
  } //ensuring (r => r.conclusion == sequent, "The merged Provable (if any) proves the conclusion this ProofNode sought " + this)

  /**
     * Whether to keep full provables or just local provables around as evidence.
     */
    private val fullProvable = false

  /**
   * The alternatives that tactics are currently trying to prove this ProofNode, i.e.
   * the given subgoal of provable.
   */
    @volatile private[this] var alternatives : List[ProofNode.ProofStep] = Nil


    /**
     * Soundness-critical invariant that all alternative proof steps have us as their goal.
     * Dropping alternatives is sound, but adding alternatives requires passing this invariant.
     */
    @elidable(ASSERTION) private def checkInvariant =
      assert(alternatives.forall(_.goal == this), "all alternatives are children of this goal")

  /**
   * The sequent that this ProofNode is trying to prove.
   */
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
     * @note Uses soundness-critical proof rule application mechanism from Provable
     *       in a non-soundness-critical but still correct way.
     */
    final def apply(rule: Rule): ProofNode.ProofStep = {
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
          ProofNode.ProofStep(newProvable, Left(rule), this, subgoals)
        } else {  // only keep subProvable around to simplify subsequent merge
          // conduct a new Provable just for the selected subgoal and apply proof rule
          val subProvable = provable.sub(subgoal)
          assert(subProvable.conclusion == sequent, "subProvable concluding our goal expected")
          val newProvable = subProvable(rule, 0)
          // a new ProofNode for each resulting subgoal
          ProofNode.ProofStep(newProvable, Left(rule), this,
            Range(0, newProvable.subgoals.length).
            map(i => new ProofNode(this, Provable.startProof(newProvable.subgoals(i)), 0)).toList)
        }
      }
      // Add as or-branching alternative
      this.synchronized {
        alternatives = alternatives :+ proofStep
      }
      checkInvariant
      proofStep
    }

  /**
   * Use the given Provable to prove this ProofNode.
   * Return the resulting list of subgoals (after including them as an or-branch alternative for proving this ProofNode).
   * @note Uses soundness-critical proof rule application mechanism from Provable
   *       in a non-soundness-critical but still correct way.
   */
  final def apply(useProvable: Provable): ProofNode.ProofStep = {
    // ProofNodes for the respective sequents resulting from applying rule to sequent.
    checkInvariant
    val proofStep = {
      assert(!fullProvable, "fullProvable not implemented")
      // only keep subProvable around to simplify subsequent merge
      // conduct a new Provable just for the selected subgoal and apply proof rule
      val subProvable = provable.sub(subgoal)
        assert(subProvable.conclusion == sequent, "subProvable concluding our goal expected")
        val newProvable = subProvable(useProvable, 0)
        // a new ProofNode for each resulting subgoal
        ProofNode.ProofStep(newProvable, Right(useProvable), this,
          Range(0, newProvable.subgoals.length).
            map(i => new ProofNode(this, Provable.startProof(newProvable.subgoals(i)), 0)).toList)
    }
    // Add as or-branching alternative
    this.synchronized {
      alternatives = alternatives :+ proofStep
    }
    checkInvariant
    proofStep
  }

    //@todo Optional: there should be a TestCase that checks that this field is never read in the prover core. But Provable already ensures soundness.
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
      !children.find((f: ProofNode.ProofStep) =>  f.isClosed).isEmpty

    /**
     * Test whether this ProofNode can be proved by merging Provable's of one of its alternatives.
     */
    def isProved(): Boolean = {
      // probably not proved if isClosed status is not even set (may be conservatively incorrect)
      if (!isClosed()) return false
      provableWitness.isProved
    }

    /**
     * Retrieves a list of open goals under this proof node.
     * @return the list of all proof nodes under this proof tree that are neither closed nor have children.
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
