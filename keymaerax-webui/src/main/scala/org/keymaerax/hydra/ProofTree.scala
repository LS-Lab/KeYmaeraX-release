/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra

import org.keymaerax.Logging
import org.keymaerax.bellerophon._
import org.keymaerax.btactics._
import org.keymaerax.btactics.macros._
import org.keymaerax.core.{
  Box,
  Expression,
  FuncOf,
  Loop,
  ODESystem,
  PredOf,
  Sequent,
  SubstitutionClashException,
  SubstitutionPair,
  USubst,
  Variable,
}
import org.keymaerax.infrastruct.Augmentors._
import org.keymaerax.infrastruct.{Position, UnificationTools}
import org.keymaerax.parser.StringConverter.StringToStringConverter
import org.keymaerax.parser.{ArchiveParser, Declaration, Location}
import org.keymaerax.pt.{ElidingProvable, ProvableSig, TermProvable}
import org.keymaerax.tacticsinterface.TraceRecordingListener

import scala.annotation.{nowarn, tailrec}
import scala.collection.immutable.{List, Map}
import scala.util.Try

trait ProofTreeNodeId {}

/**
 * A Proof Tree Node represents the central element of managing a (possibly large compound) inference during proof
 * search in a [[ProofTree]]. Unlike the stateless [[org.keymaerax.core.Provable]] representation of the prover kernel,
 * proof trees provide navigation and tactic scheduling infrastructure.
 *
 * Beyond providing proof tree navigation information, this type manages the interface to the kernel's provable. Proof
 * tree nodes consist of a local provable that created this proof node, and which can later be stitched together after
 * completing the entire subproof. The [[provable]] function can later perform the computation required to staple the
 * proof together as far as the children have completed it.
 *
 * The proof treee node also provides infrastructure for letting tactics run to expand this proof tree node.
 * @see
 *   [[org.keymaerax.core.Provable]]
 * @see
 *   [[ProvableSig]]
 */
trait ProofTreeNode {
  // proof tree node identifier information

  /** The node ID. */
  val id: ProofTreeNodeId

  /** The proof that this proof node is a part of. */
  val proof: ProofTree

  // kernel interface with actual provables that this proof tree node contains

  /**
   * The local provable, whose subgoals will be filled in by the node's [[children]].
   * @see
   *   [[provable]]
   */
  def localProvable: ProvableSig

  /** The tree node's conclusion (might be subject to other nodes being proved). */
  final def conclusion: Sequent = localProvable.conclusion

  /**
   * Compute the overall provable with the sub-proofs already filled in for the local subgoals (potentially expensive)
   * from [[children]].
   * @see
   *   [[localProvable]]
   */
  final def provable: ProvableSig = theProvable

  /**
   * Indicates whether or not the proof from this node downwards is done (potentially expensive).
   * @see
   *   [[ProvableSig.isProved]]
   */
  final def isProved: Boolean = provable.isProved

  // proof tree navigation

  /** The node's parent, None if root. */
  def parent: Option[ProofTreeNode]

  /** The node's direct children. */
  def children: List[ProofTreeNode]

  /** All direct and indirect descendants of this node. */
  def allDescendants: List[ProofTreeNode] = theDescendants

  /** All direct and indirect ancestors of this node. */
  def allAncestors: List[ProofTreeNode] = theAncestors

  /** The number of subgoals in the local provable (fast, doesn't actually load the provable). */
  def numSubgoals: Int

  /**
   * The tactic (serialized BelleExpr) that produced this node from its parent.
   * @ensures
   *   \result == None <-> parent == None
   */
  def maker: Option[String]

  // meta info

  /** The tactic short name. */
  def makerShortName: Option[String]

  /** Uniform substitutions applied at this node. */
  def substs: List[SubstitutionPair] = makerSubst(maker)

  /** The node label. */
  def label: Option[BelleLabel]

  /** The node's goal, None if closed. */
  def goal: Option[Sequent]

  /** The index of the goal (subgoal in local provable) that this node targets. */
  def goalIdx: Int

  // tactic application or proof tree manipulation at this proof tree node

  /** Deletes this node with the entire subtree underneath. */
  def pruneBelow(): Unit

  /**
   * Returns a list of tactics that are applicable at the specified position in this node's goal. Each entry is the
   * typical form of the tactic and an optional more convenient variant of the tactic.
   */
  def applicableTacticsAt(
      pos: Position,
      pos2: Option[Position] = None,
  ): List[(DerivationInfo, Option[DerivationInfo])] = pos2 match {
    case None =>
      // single-position tactics
      goal.map(g => (g, g.sub(pos))) match {
        case Some((goal, Some(subFormula))) => UIIndex
            .allStepsAt(subFormula, Some(pos), Some(goal), proof.substs)
            .map(axiom => (axiom, UIIndex.comfortOf(axiom.codeName)))
        case _ => Nil
      }
    case Some(p2) =>
      // two-pos tactics
      UIIndex.allTwoPosSteps(pos, p2, goal.get).map(step => (step, UIIndex.comfortOf(step.codeName)))
  }

  /** Returns suggestions for tactic argument inputs, argument info according to UIIndex and DerivationInfo. */
  def tacticInputSuggestions(pos: Position): Map[ArgInfo, Expression]

  /** Runs a tactic on this node. */
  // @todo shortName should be derived from tactic
  // @todo interpreter/listener interface needs revision
  def runTactic(
      userId: String,
      interpreter: List[IOListener] => Interpreter,
      tactic: BelleExpr,
      shortName: String,
      executor: BellerophonTacticExecutor = BellerophonTacticExecutor.defaultExecutor,
      wait: Boolean = false,
  ): String

  /** Runs a tactic step-by-step, starting on this node. */
  def stepTactic(
      userId: String,
      interpreter: Interpreter,
      tactic: BelleExpr,
      executor: BellerophonTacticExecutor = BellerophonTacticExecutor.defaultExecutor,
      wait: Boolean = false,
  ): String

  // internals

  /** Applies derivation `sub` to subgoal  `i` of `goal`. Expands substitutions if necessary before applying `sub`. */
  private def applySub(goal: ProvableSig, sub: ProvableSig, i: Int): ProvableSig = {

    /**
     * Apply sub to goal.
     * @note
     *   sub may originate from a lemma that was proved with expanded definitions, find expanded substitutions. both may
     *   have applied partial substitutions separately, e.g., goal gt(x,y^2) |- gt(x,y^2) and sub x>sq(y) |- x>sq(y)
     */
//    @tailrec
//    def applySub(goal: ProvableSig, sub: ProvableSig): ProvableSig = {
//      val allSubsts = (proof.substs ++ proof.proofSubsts).distinct
//      val allSymbols = StaticSemantics.symbols(goal.subgoals(i)) ++ StaticSemantics.symbols(sub.conclusion)
//      val symbols = allSymbols -- StaticSemantics.symbols(goal.subgoals(i)).intersect(StaticSemantics.symbols(sub.conclusion))
//      val substs = USubst(allSubsts.filter({ case SubstitutionPair(what, _) => symbols.intersect(StaticSemantics.symbols(what)).nonEmpty }))
//      val substGoal = exhaustiveSubst(goal, substs)
//      val substSub = exhaustiveSubst(sub, substs)
//      if (substGoal.subgoals(i) == substSub.conclusion) substGoal(substSub, i)
//      else applySub(substGoal, substSub)
//    }

    if (goal.subgoals(i) == sub.conclusion) goal(sub, i)
    else {
      val allSubsts = (proof.substs ++ proof.proofSubsts).distinct
      val substs = UnificationTools.collectSubst(goal.underlyingProvable, i, sub.underlyingProvable, allSubsts)
      try { exhaustiveSubst(goal, substs)(exhaustiveSubst(sub, substs), i) }
      catch {
        case ex: SubstitutionClashException
            if ex.e.asTerm.isInstanceOf[Variable] && ex.context.asTerm.isInstanceOf[FuncOf] =>
          // @note proof step introduced function symbols with delayed substitution,
          // but may not yet be done and so back-substitution fails
          goal
      }
    }
  }

  // cached computations

  /** Merges all descendent provables into the local provable. */
  private lazy val theProvable: ProvableSig = {
    if (localProvable.isProved) localProvable else applySub(localProvable, mergedDescendentProvable, goalIdx)
  }

  /** Creates intermediate provables for all descendents of the shape mergable into the local provable's subgoal. */
  private lazy val mergedDescendentProvable: ProvableSig = {
    if (localProvable.isProved) localProvable
    else if (children.isEmpty)
      localProvable.sub(goalIdx) // @note if no followup proof step happened, then return stuttering proof step
    else {
      // the provable representing our proof step is the localProvable stored in all children (for lookup performance)
      // myProvable := obtain the unique localProvable that all children agree on, because they are off to prove its respective subgoals
      // @todo should become part of the documentation of the respective methods
      val myProvable = children.head.localProvable
      assert(
        children.forall(_.localProvable == myProvable),
        "All children share the same local provable, only differing in goalIdx",
      )

      // merge finalized provables from all children into local provable;
      // if they cannot be merged verbatim, merge by delayed substitution;
      // if they cannot be merged (backsubstitution failed, see SequentialInterpreter Let): keep global
      if (myProvable.isProved) { myProvable }
      else children
        .map(_.mergedDescendentProvable)
        .zipWithIndex
        .foldRight(myProvable)({ case ((sub, i), global) => applySub(global, sub, i) })
    }
  }

  /** Applies substitutions `s` to provable `p` exhaustively. */
  @tailrec
  private def exhaustiveSubst(p: ProvableSig, s: USubst): ProvableSig = {
    val substituted = p(s)
    if (substituted != p) exhaustiveSubst(substituted, s) else substituted
  }

  private lazy val usMatcher = """(?<!by)US\("(?<subst>[^"]*)"\)""".r
  private lazy val expandMatcher = """expand\s*"(?<name>[^"]*)"""".r

  /** Extracts the substitution from a tactic string (None if the tactic string is not a uniform substitution). */
  private def makerSubst(maker: Option[String]): List[SubstitutionPair] = maker
    .map(m => {
      if (m.contains("expandAllDefs")) { proof.substs }
      else if (m.contains("expand \"")) {
        expandMatcher
          .findAllMatchIn(m)
          .map(_.group("name"))
          .flatMap(n =>
            proof
              .substs
              .find(_.what match {
                case FuncOf(fn, _) => fn.prettyString == n
                case PredOf(fn, _) => fn.prettyString == n
                case _ => false
              })
          )
          .toList
      } else if (m.contains("US(")) {
        import org.keymaerax.parser.StringConverter._
        // collect substitutions of expandAll (serializes to sequence of US), and
        // anywhere in custom tactics, e.g., "expand Q; unfold; expand P; auto"
        usMatcher.findAllMatchIn(m).map(_.group("subst").trim).map(_.asSubstitutionPair).toList.distinct
      } else Nil
    })
    .getOrElse(Nil)

  private lazy val theDescendants = children ++ children.flatMap(_.allDescendants)
  private lazy val theAncestors = parent.toList ++ parent.map(_.allAncestors).getOrElse(Nil)
}

/**
 * The central proof tree data structure managing the proof search, consisting of a set of [[ProofTreeNode]]. Unlike the
 * stateless [[org.keymaerax.core.Provable]] representation of the prover kernel, proof trees provide navigation and
 * tactic scheduling infrastructure.
 * @see
 *   [[org.keymaerax.core.Provable]]
 * @see
 *   [[ProvableSig]]
 */
trait ProofTree {

  /**
   * Verify that the proof is closed by constructing a proved provable.
   * @ensures
   *   \result==root.provable.isProved
   * @see
   *   [[ProofTreeNode.isProved]]
   * @see
   *   [[done]]
   */
  def isProved: Boolean = { load(); root.provable.isProved }

  // proof tree navigation

  /** The root node with the desired conclusion of this proof tree */
  def root: ProofTreeNode

  /** All proof nodes anywhere in the proof tree, including root, inner nodes, and leaves. */
  def nodes: List[ProofTreeNode]

  /** The proof's leaves (open and closed) */
  def leaves: List[ProofTreeNode]

  /** The proof's open goals, which are the leaves that are not done yet */
  def openGoals: List[ProofTreeNode]

  /**
   * Lightweight check indicating, if true, that the proof database representation thinks it might be closed (not
   * verified by core yet).
   * @see
   *   [[isProved]]
   */
  def done: Boolean

  /**
   * Locates a node in the proof tree by its ID.
   * @see
   *   noteIdFromString(String)
   */
  def locate(id: ProofTreeNodeId): Option[ProofTreeNode]

  /**
   * Locates a node in the proof tree by its ID (string representation).
   * @see
   *   noteIdFromString(String)
   * @see
   *   [[locate(ProofTreeNodeId)]]
   */
  def locate(id: String): Option[ProofTreeNode] = nodeIdFromString(id).flatMap(locate)

  /**
   * Converts a string representation to a node ID.
   * @see
   *   [[locate(ProofTreeNodeId)]]
   */
  def nodeIdFromString(id: String): Option[ProofTreeNodeId]

  /**
   * Prefetch all nodes in a proof tree from the database. Does not include provables by default (expensive to load).
   * The resulting ProofTree is functionally equivalent to this tree but provides fast access.
   */
  def load(withProvables: Boolean = false): ProofTree

  // tactical information

  /**
   * String representation (including location to node mapping) of the global tactic that reproduces this whole proof
   * tree from the conjecture at the root (very expensive). Uses `converter` to turn the recorded steps into a tactic.
   */
  def tacticString(converter: TraceToTacticConverter): (String, Map[Location, ProofTreeNode])

  /** The global tactic that reproducse this whole proof tree from the conjecture at the root (very expensive) */
  def tactic: BelleExpr

  /** The proof info with meta information about this proof, e.g., its name. */
  def info: ProofPOJO

  /** Substitutions known from the input model. */
  def substs: List[SubstitutionPair]

  /** Substitutions from proof steps. */
  def proofSubsts: List[SubstitutionPair]

  override def toString: String = printBelow(root, "")

  private def printBelow(node: ProofTreeNode, indent: String): String = {
    indent + node.id + "\n" + node.children.map(printBelow(_, indent + "  ")).mkString("\n")
  }
}

abstract class ProofTreeBase(val proofId: String) extends ProofTree {}

/** Identifies a proof tree node by the parent step + branch index. */
case class DbStepPathNodeId(step: Option[Int], branch: Option[Int]) extends ProofTreeNodeId {
  override def toString: String = step match {
    case None => "()"
    case Some(pId) => branch match {
        case None => s"($pId)"
        case Some(bIdx) => s"($pId,$bIdx)"
      }
  }
}

/**
 * A [[ProofTreeNode]] that happens to be stored in the database `db`.
 * @param db
 *   The database that this proof tree node is stored in.
 * @param proof
 *   the proof that this proof tree node belongs to.
 */
abstract class DbProofTreeNode(db: DBAbstraction, val proof: ProofTree) extends ProofTreeNode {

  /** Runs a tactic on this node. */
  override def runTactic(
      userId: String,
      interpreter: List[IOListener] => Interpreter,
      tactic: BelleExpr,
      shortName: String,
      executor: BellerophonTacticExecutor = BellerophonTacticExecutor.defaultExecutor,
      wait: Boolean = false,
  ): String = {
    assert(goalIdx >= 0, "Cannot execute tactics on closed nodes without open subgoal")
    val pr = localProvable.reapply(proof.info.defs(db))
    val listener = new TraceRecordingListener(
      db,
      proof.info.proofId,
      stepId,
      pr,
      goalIdx,
      recursive = false,
      shortName,
      constructGlobalProvable = false,
    )
    val taskId = executor.schedule(
      userId,
      tactic,
      BelleProvable.labeled(pr.sub(goalIdx), label.map(_ :: Nil)),
      interpreter(listener :: Nil),
    )
    if (wait) {
      executor.wait(taskId)
      executor.getResult(taskId) match {
        case Some(Right(ex)) => throw ex
        case _ => // either cancelled or succeeded
      }
    }
    taskId
  }

  /** Runs a tactic step-by-step, starting on this node. */
  override def stepTactic(
      userId: String,
      interpreter: Interpreter,
      tactic: BelleExpr,
      executor: BellerophonTacticExecutor = BellerophonTacticExecutor.defaultExecutor,
      wait: Boolean = false,
  ): String = {
    assert(goalIdx >= 0, "Cannot execute tactics on closed nodes without open subgoal")
    val pr = localProvable.reapply(proof.info.defs(db))
    val taskId = executor.schedule(userId, tactic, BelleProvable(pr.sub(goalIdx), label.map(_ :: Nil)), interpreter)
    if (wait) {
      executor.wait(taskId)
      // report tactic execution problems upon completion
      executor.getResult(taskId) match {
        case Some(Right(ex)) => throw ex
        case _ => // either cancelled or succeeded
      }
    }
    taskId
  }

  /** The node's goal */
  override def goal: Option[Sequent] = id match {
    case DbStepPathNodeId(_, None) =>
      assert(localProvable.subgoals.size <= 1, "Node without branch only for provables with sole subgoal")
      localProvable.subgoals.headOption
    case DbStepPathNodeId(_, Some(branch)) => if (localProvable.isProved) None else Some(localProvable.subgoals(branch))
  }

  /** The index of the goal (subgoal in local provable) that this node targets. */
  override def goalIdx: Int = id match {
    case DbStepPathNodeId(_, None) => 0 // @note root node
    case DbStepPathNodeId(_, Some(i)) => i
  }

  override def tacticInputSuggestions(pos: Position): Map[ArgInfo, Expression] = goal.map(g => (g, g.sub(pos))) match {
    case Some((goal, Some(subFormula))) =>
      // @HACK assumes that the currently loaded proof and this tree's proof are the same
      //      to avoid reparsing the model on every call to tacticInputSuggestions.
      val generator = TactixLibrary.invSupplier
      // @todo extend generator to generate for named arguments j(x), R, P according to tactic info
      // @HACK for loop and dG
      subFormula match {
        case Box(Loop(_), _) =>
          // @todo provide model definitions
          val invariant = generator.generate(goal, pos, Declaration(Map.empty)).iterator
          if (invariant.hasNext) Map(FormulaArg("J") -> invariant.next().formula) else Map.empty
        case Box(_: ODESystem, p) => Map(FormulaArg("P", List("y")) -> p) // @hack for dG
        case _ => Map.empty
      }
    case Some((_, None)) => Map.empty
    case None => Map.empty
  }

  /** Deletes this node with the entire subtree underneath. */
  @nowarn("msg=match may not be exhaustive")
  override def pruneBelow(): Unit = children match {
    case Nil => // nothing to do
    case (c: DbProofTreeNode) :: tail =>
      assert(tail.forall(_.asInstanceOf[DbProofTreeNode].stepId == c.stepId), "Expected same step in all children")
      db.deleteExecutionStep(proof.info.proofId, c.stepId.get) // @note database does cascade delete of all substeps
  }

  /** Execution step recording: predecessor step ID. */
  protected def stepId: Option[Int]
}

object DbPlainExecStepProofTreeNode extends Logging {

  /**
   * Initializes a proof tree node from a recorded execution step. The branch identifies the subgoal created by the
   * execution step. If None, the node refers to the step's source (parent) node.
   */
  def fromExecutionStep(
      db: DBAbstraction,
      proof: ProofTree,
  )(step: ExecutionStepPOJO, branch: Option[Int]): DbPlainExecStepProofTreeNode = branch match {
    case None => DbPlainExecStepProofTreeNode(
        db,
        DbStepPathNodeId(step.previousStep, Some(step.branchOrder)),
        proof,
        () => {
          logger.debug("WARNING: ripple loading (node parent)");
          db.getPlainExecutionStep(proof.info.proofId, step.previousStep.get).get
        },
      )
    case Some(b) => DbPlainExecStepProofTreeNode(db, DbStepPathNodeId(step.stepId, Some(b)), proof, () => step)
  }

  /** Initializes a proof tree node from a recorded execution step. */
  def fromExecutionStep(db: DBAbstraction, proof: ProofTree, step: ExecutionStepPOJO): DbPlainExecStepProofTreeNode = {
    DbPlainExecStepProofTreeNode(db, DbStepPathNodeId(step.stepId, None), proof, () => step)
  }
}

/**
 * A proof tree node backed by a database of recorded execution steps. An ID Some(step),None points to the source node
 * where step was executed, an ID Some(step),Some(branch) represents a proxy for the branch subgoal created by step and
 * searches the actual successor step on demand.
 */
case class DbPlainExecStepProofTreeNode(
    db: DBAbstraction,
    override val id: ProofTreeNodeId,
    override val proof: ProofTree,
    stepLoader: () => ExecutionStepPOJO,
) extends DbProofTreeNode(db, proof) with Logging {

  /** Loads the step on demand. */
  private lazy val step = stepLoader()

  /** The node's parent, None if root. */
  override def parent: Option[ProofTreeNode] = dbParent

  /** The node's children. */
  override def children: List[ProofTreeNode] = dbSubgoals

  /** The tactic that produced this node from its parent. */
  override def maker: Option[String] = Some(dbMaker)

  /** The tactic short name. */
  override def makerShortName: Option[String] = Some(step.ruleName)

  /** The node label. */
  override def label: Option[BelleLabel] = step.branchLabel.flatMap(BelleLabel.fromString(_).lift(goalIdx))

  /** A local provable, whose subgoals are filled in by the node's children. */
  override def localProvable: ProvableSig = dbLocalProvable

  /** The number of subgoals in the local provable (fast, doesn't actually load the provable). */
  override def numSubgoals: Int = step.numSubgoals

  /** Execution step recording: predecessor step ID (=this, when executing a tactic on this). */
  override protected def stepId: Option[Int] = id match { case DbStepPathNodeId(stId, _) => stId }

  private lazy val dbMaker = {
    logger.debug(s"Node $id: querying maker")
    db.getExecutable(step.executableId).belleExpr
  }

  private lazy val dbParent = step.previousStep match {
    case None => Some(DbRootProofTreeNode(db)(DbStepPathNodeId(None, None), proof))
    case Some(pId) =>
      logger.debug(s"Node $id: querying parent")
      // this step knows on which branch it was executed
      val parentBranch = db.getPlainExecutionStep(proof.info.proofId, stepId.get).map(_.branchOrder)
      Some(DbPlainExecStepProofTreeNode(
        db,
        DbStepPathNodeId(Some(pId), parentBranch),
        proof,
        () => {
          logger.debug("WARNING: ripple loading (parent " + pId + ")");
          db.getPlainExecutionStep(proof.info.proofId, pId).get
        },
      ))
  }

  private lazy val dbSubgoals = {
    logger.debug(s"Node $id: querying subgoals")
    // subgoals are the steps that have this.stepId as previousStep and this.goalIdx as branchOrder
    val successors = db.getPlainStepSuccessors(proof.info.proofId, stepId.get, goalIdx)
    assert(successors.size <= 1, "Expected unique successor step for node " + id + ", but got " + successors)
    val successorSteps = successors.flatMap(s => db.getPlainExecutionStep(proof.info.proofId, s.stepId.get))
    successorSteps.flatMap(s =>
      if (s.numSubgoals > 0)
        (0 until s.numSubgoals).map(sgi => DbPlainExecStepProofTreeNode.fromExecutionStep(db, proof)(s, Some(sgi)))
      else DbPlainExecStepProofTreeNode.fromExecutionStep(db, proof)(s, Some(-1)) :: Nil
    )
  }

  private lazy val dbLocalProvable = db.getProvable(step.localProvableId.get).provable match {
    // database does not store definitions of provables
    case ep: ElidingProvable => ep.copy(defs = proof.info.defs(db))
    case tp: TermProvable => tp.copy(defs = proof.info.defs(db))
  }
}

/** A loaded node (root if step=None, then also parent=None, maker=None, makerShortName=None). */
case class DbLoadedProofTreeNode(
    db: DBAbstraction,
    override val id: ProofTreeNodeId,
    override val proof: ProofTree,
    override val children: List[ProofTreeNode],
    step: Option[ExecutionStep],
) extends DbProofTreeNode(db, proof) {

  /** Build tree */
  children.foreach({
    case c: DbLoadedProofTreeNode => c.theParent = Some(this)
    case _ =>
  })

  /** The node's parent, None if root. */
  override def parent: Option[ProofTreeNode] = theParent

  /** The tactic (serialized BelleExpr) that produced this node from its parent. */
  override def maker: Option[String] = step.map(_ => dbMaker) // @todo load with step

  @nowarn("msg=match may not be exhaustive")
  private val nameLabel: Option[(String, List[BelleLabel])] = step.map(_.rule.split("@@").toList match {
    case rn :: Nil => (rn, Nil)
    case rn :: bl :: Nil => (rn, BelleLabel.fromString(bl))
  })

  /** The tactic short name. */
  override def makerShortName: Option[String] = nameLabel.map(_._1)

  /** The node label. */
  override def label: Option[BelleLabel] = step match {
    case None => None
    case Some(_) => nameLabel.flatMap(_._2.lift(goalIdx))
  }

  /**
   * A local provable, whose subgoals are filled in by the node's children. Triggers a database operation if the node's
   * step is loaded without provables.
   */
  override def localProvable: ProvableSig = step match {
    case None => db.getProvable(proof.info.provableId.get).provable
    case Some(s) => s.local
  }

  /** The number of subgoals in the local provable (fast, doesn't actually load the provable). */
  override def numSubgoals: Int = localProvable.subgoals.size

  /** Execution step recording: predecessor step ID. */
  override protected def stepId: Option[Int] = step.map(_.stepId)

  /** Loaded parent */
  private var theParent: Option[ProofTreeNode] = None

  private lazy val dbMaker = step match {
    case None => ""
    case Some(s) => db.getExecutable(s.executableId).belleExpr
  }
}

case class DbRootProofTreeNode(db: DBAbstraction)(override val id: ProofTreeNodeId, override val proof: ProofTree)
    extends DbProofTreeNode(db, proof) {

  /** The node's parent, None if root. */
  override def parent: Option[ProofTreeNode] = None

  /** The node's children. */
  override def children: List[ProofTreeNode] = theSubgoals

  /** The tactic (serialized BelleExpr) that produced this node from its parent. */
  override def maker: Option[String] = None

  /** The tactic short name. */
  override def makerShortName: Option[String] = None

  /** The node label. */
  override def label: Option[BelleLabel] = None

  /** A local provable, whose subgoals are filled in by the node's children. */
  override def localProvable: ProvableSig = dbLocal

  /** The number of subgoals in the local provable (fast, doesn't actually load the provable). */
  override def numSubgoals: Int = 1

  /** Execution step recording: predecessor step ID. */
  override protected def stepId: Option[Int] = None

  // cached database query results
  private lazy val theSubgoals: List[ProofTreeNode] = {
    db.getFirstExecutionStep(proof.info.proofId) match {
      case None => Nil
      case Some(step) =>
        val s = db.getPlainExecutionStep(proof.info.proofId, step.stepId.get).get
        if (s.numSubgoals > 0) (0 until s.numSubgoals)
          .map(sgi => DbPlainExecStepProofTreeNode.fromExecutionStep(db, proof)(s, Some(sgi)))
          .toList
        else DbPlainExecStepProofTreeNode.fromExecutionStep(db, proof)(s, Some(-1)) :: Nil
    }
  }

  private lazy val dbLocal = db.getProvable(proof.info.provableId.get).provable
}

/**
 * Builds proof trees from database-recorded step executions, starting at the specified root step (None: proof root).
 */
case class DbProofTree(db: DBAbstraction, override val proofId: String) extends ProofTreeBase(proofId) {

  /** Locates a node in the proof tree relative to its parent. */
  override def locate(id: ProofTreeNodeId): Option[ProofTreeNode] = id match {
    case DbStepPathNodeId(None, _) => Some(DbRootProofTreeNode(db)(DbStepPathNodeId(None, None), this))
    case DbStepPathNodeId(Some(stepId), branch) => db
        .getPlainExecutionStep(proofId.toInt, stepId)
        .map(DbPlainExecStepProofTreeNode.fromExecutionStep(db, this)(_, branch))
  }

  /** Locates the tree root. */
  override def root: ProofTreeNode = loadedRoot match {
    case None => dbRoot
    case Some(root) => root
  }

  private def stepNodes(steps: List[(ExecutionStepPOJO, List[Int])]): List[ProofTreeNode] = {
    // @note alternative that loads the entire trace in case the plainOpenSteps outer join becomes slow again
    //    val trace = dbTrace
    //    // a final step is one that doesn't have a successor for each of its subgoals
    //    val finalSteps = trace.filter(parent => trace.count(s => parent.stepId == s.previousStep) < parent.numSubgoals)
    //    // final step and non-covered branches
    //    val finalOpenBranches = finalSteps.map(f => f ->
    //      ((0 until f.numSubgoals).toSet -- trace.filter(s => f.stepId == s.previousStep).map(_.branchOrder)).toList)

    val openBranches = steps.map({ case (f, closed) => f -> ((0 until f.numSubgoals).toSet -- closed).toList })

    val goalNodes: List[ProofTreeNode] =
      if (root.children.isEmpty && !root.isProved) List(root)
      else openBranches.flatMap({ case (fs, subgoals) =>
        if (fs.numSubgoals > 0)
          subgoals.map(sgi => DbPlainExecStepProofTreeNode.fromExecutionStep(db, this)(fs, Some(sgi)))
        // closed proofs without subgoals
        else List(DbPlainExecStepProofTreeNode.fromExecutionStep(db, this, fs))
      })

    goalNodes
  }

  /** @inheritdoc */
  override def openGoals: List[ProofTreeNode] = stepNodes(dbOpenGoals)

  /** @inheritdoc */
  override def leaves: List[ProofTreeNode] = stepNodes(dbLeaves)

  /** All proof nodes, in order of step execution. */
  override def nodes: List[ProofTreeNode] = { load(); loadedNodes }

  /** The tactic to produce this tree from its root conclusion. */
  override def tacticString(converter: TraceToTacticConverter): (String, Map[Location, ProofTreeNode]) = {
    load()
    converter.getTacticString(this)
  }

  /** @inheritdoc */
  override def tactic: BelleExpr = ArchiveParser
    .tacticParser(tacticString(new VerboseTraceToTacticConverter(dbDefs))._1)

  /** Indicates whether or not the proof might be closed. */
  override def done: Boolean = dbProofInfo.closed

  /** Returns a loaded proof tree to avoid ripple loading. */
  override def load(withProvables: Boolean = false): ProofTree = {
    val trace = db.getExecutionTrace(proofId.toInt, withProvables)

    // DB step is a tuple [id,previd,branch,tactic,provable,n,...]
    // which translates into n nodes (id,0,tactic,provable)...(id,n-1,tactic,provable),
    // each being a child of node (previd,branch), created by tactic
    // node (id,0)'s goal=provable.sub(0), (id,n-1)'s goal=provable.sub(n-1)

    val linkedStepNodes = trace
      .steps
      .foldRight(Map[ProofTreeNodeId, List[ProofTreeNode]]())({ case (s, children) =>
        val stepResultNodes: List[ProofTreeNode] =
          if (s.subgoalsCount > 0) (0 until s.subgoalsCount)
            .map(i =>
              DbLoadedProofTreeNode(
                db,
                DbStepPathNodeId(Some(s.stepId), Some(i)),
                this,
                children.getOrElse(DbStepPathNodeId(Some(s.stepId), Some(i)), Nil),
                Some(s),
              )
            )
            .toList
          else
            DbLoadedProofTreeNode(db, DbStepPathNodeId(Some(s.stepId), None), this, Nil, Some(s)) ::
              Nil // QE, close etc.

        children + (DbStepPathNodeId(s.prevStepId, Some(s.branch)) -> stepResultNodes)
      })

    loadedRoot = Some(DbLoadedProofTreeNode(
      db,
      DbStepPathNodeId(None, None),
      this,
      linkedStepNodes.getOrElse(DbStepPathNodeId(None, Some(0)), Nil),
      None,
    ))

    loadedNodes = loadedRoot.get ::
      linkedStepNodes
        .values
        .flatten
        .toList
        .sortBy(_.id match { case DbStepPathNodeId(stepId, branch) => (stepId, branch) })

    this
  }

  /** The proof info. */
  override def info: ProofPOJO = dbProofInfo

  /** The known substitutions. */
  override def substs: List[SubstitutionPair] = dbSubsts

  /** @inheritdoc */
  override def proofSubsts: List[SubstitutionPair] = this.nodes.flatMap(_.substs)

  /** Converts a string representation to a node ID. */
  override def nodeIdFromString(id: String): Option[ProofTreeNodeId] =
    if (id == "()") Some(DbStepPathNodeId(None, None))
    else {
      Try(id.stripPrefix("(").stripSuffix(")").split(",").map(_.toInt)).toOption match {
        case Some(pathElems) if pathElems.length == 2 =>
          Some(DbStepPathNodeId(Some(pathElems.head), Some(pathElems.last)))
        case _ => None
      }

    }

  // cached db query results
  private lazy val dbProofInfo = db.getProofInfo(proofId)

  private lazy val dbDefs = info.defs(db)

  private lazy val dbSubsts = dbDefs.substs

  private lazy val dbRoot = locate(DbStepPathNodeId(None, None)).get

  private lazy val dbOpenGoals = db.getPlainOpenSteps(proofId.toInt)

  private lazy val dbLeaves = db.getPlainLeafSteps(proofId.toInt)

  private var loadedRoot: Option[ProofTreeNode] = None

  private var loadedNodes: List[ProofTreeNode] = Nil
}

case class AgendaItem(id: String, name: String, proofId: String, ancestors: List[String] = Nil) {
  def path: List[String] = id +: ancestors
}

object AgendaItem {

  /** Creates a name from the deriviation info of `codeName`. */
  def nameOf(codeName: String): String = {
    Try(DerivationInfo.ofCodeName(codeName)).toOption match {
      case Some(di) => di.display.names.name
      case None => codeName
    }
  }

  /** Creates a name from a proof tree node. */
  def nameOf(node: ProofTreeNode): String = {
    if (node.parent.exists(_.id.toString == "()")) "Conjecture: "
    else nameOf(node.makerShortName.getOrElse("").split("\\(").head)
  }
}
