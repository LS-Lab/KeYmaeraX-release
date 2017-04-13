package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.core.{Box, Expression, Loop, ODESystem, Sequent}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tacticsinterface.TraceRecordingListener

import scala.collection.immutable.{List, Map}
import scala.util.Try

trait ProofTreeNodeId {}

trait ProofTreeNode {
  /** The node ID. */
  val id: ProofTreeNodeId

  /** The proof this node is a part of. */
  val proofId: String

  /** The node's parent, None if root. */
  def parent: Option[ProofTreeNode]

  /** The node's direct children. */
  def children: List[ProofTreeNode]

  /** All direct and indirect descendants of this node. */
  def allDescendants: List[ProofTreeNode] = theDescendants

  /** The number of subgoals in the local provable (fast, doesn't actually load the provable). */
  def numSubgoals: Int

  /** The tactic (serialized BelleExpr) that produced this node from its parent. */
  def maker: Option[String]

  /** The tactic short name. */
  def makerShortName: Option[String]

  /** A local provable, whose subgoals are filled in by the node's children. */
  def localProvable: ProvableSig

  /** The tree node's conclusion (might be subject to other nodes being proved). */
  def conclusion: Sequent = localProvable.conclusion

  /** The node's goal, None if closed. */
  def goal: Option[Sequent]

  /** The index of the goal (subgoal in local provable) that this node targets. */
  def goalIdx: Int

  /** Returns a list of tactics that are applicable at the specified position in this node's goal. Each entry is
    * the typical form of the tactic and an optional more convenient variant of the tactic. */
  def applicableTacticsAt(pos: Position, pos2: Option[Position] = None): List[(DerivationInfo, Option[DerivationInfo])] = pos2 match {
    case None =>
      // single-position tactics
      goal.map(g => (g, g.sub(pos))) match {
        case Some((goal, Some(subFormula))) =>
          UIIndex.allStepsAt(subFormula, Some(pos), Some(goal)).map(axiom =>
            (DerivationInfo(axiom), UIIndex.comfortOf(axiom).map(DerivationInfo(_))))
        case _ => Nil
      }
    case Some(p2) =>
      // two-pos tactics
      UIIndex.allTwoPosSteps(pos, p2, goal.get).map(step =>
        (DerivationInfo.ofCodeName(step), UIIndex.comfortOf(step).map(DerivationInfo.ofCodeName)))
  }

  /** Returns suggestions for tactic argument inputs, argument info according to UIIndex and DerivationInfo. */
  def tacticInputSuggestions(pos: Position): Map[ArgInfo, Expression]

  /** The overall provable with the sub-proofs filled in for the local subgoals (potentially expensive). */
  def provable: ProvableSig = theProvable

  /** Indicates whether or not the proof from this node downwards is done (potentially expensive). */
  def done: Boolean = provable.isProved

  /** Runs a tactic on this node. */
  def runTactic(userId: String, interpreter: List[IOListener]=>Interpreter, tactic: BelleExpr, shortName: String,
                wait: Boolean = false): String

  /** Deletes this node with the entire subtree underneath. */
  def pruneBelow(): Unit

  // cached computations
  private lazy val theProvable = {
    if (localProvable.isProved) localProvable
    else if (children.isEmpty) localProvable.sub(goalIdx)
    else {
      assert(children.forall(_.localProvable == children.head.localProvable), "All children share the same local provable")
      val nextStepProvable = children.head.localProvable
      val myGoal = localProvable.sub(goalIdx)
      assert(myGoal.subgoals.head == nextStepProvable.conclusion, "Expected next step to prove my goal")

      val myProvable = myGoal(nextStepProvable, 0)
      if (myProvable.isProved) myProvable
      else children.map(_.provable).zipWithIndex.foldRight(myProvable)({ case ((sub, i), global) =>
        global(sub, i)
      })
    }
  }

  private lazy val theDescendants = children ++ children.flatMap(_.allDescendants)
}

trait ProofTree {
  /** Locates a node in the proof tree by its ID. */
  def locate(id: ProofTreeNodeId): Option[ProofTreeNode]

  /** Locates a node in the proof tree by its ID (string representation). */
  def locate(id: String): Option[ProofTreeNode] = nodeIdFromString(id).flatMap(locate)

  /** Locates the tree root. */
  def root: ProofTreeNode

  /** All proof nodes */
  def nodes: List[ProofTreeNode]

  /** The proof's open goals */
  def openGoals: List[ProofTreeNode]

  /** The tactic to produce this tree from its root conclusion. */
  def tacticString: String

  /** The tactic to produce this tree from its root conclusion. */
  def tactic: BelleExpr = BelleParser(tacticString)

  /** Indicates whether or not the proof might be closed. */
  def isClosed: Boolean

  /** The proof info. */
  def info: ProofPOJO

  /** Returns a loaded proof tree to avoid ripple loading. Does not include provables by default (expensive to load). */
  def load(withProvables: Boolean=false): ProofTree

  /** Verify that the proof is closed by constructing a proved provable. */
  def verifyClosed: Boolean = { load(); root.provable.isProved }

  /** Converts a string representation to a node ID. */
  def nodeIdFromString(id: String): Option[ProofTreeNodeId]

  override def toString: String = printBelow(root, "")

  private def printBelow(node: ProofTreeNode, indent: String): String = {
    indent + node.id + "\n" + node.children.map(printBelow(_, indent + "  ")).mkString("\n")
  }
}

abstract class ProofTreeBase(val proofId: String) extends ProofTree {

}

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

abstract class DbProofTreeNode(db: DBAbstraction, val proofId: String) extends ProofTreeNode {
  /** Runs a tactic on this node. */
  override def runTactic(userId: String, interpreter: (List[IOListener]) => Interpreter, tactic: BelleExpr,
                         shortName: String, wait: Boolean = false): String = {
    assert(goalIdx >= 0, "Cannot execute tactics on closed nodes without open subgoal")
    val listener = new TraceRecordingListener(db, proofId.toInt, stepId, localProvable,
      goalIdx, recursive = false, shortName)
    val executor = BellerophonTacticExecutor.defaultExecutor
    val taskId = executor.schedule(userId, tactic, BelleProvable(localProvable.sub(goalIdx)),
      SequentialInterpreter(listener::Nil))
    if (wait) executor.wait(taskId)
    taskId
  }

  /** The node's goal */
  override def goal: Option[Sequent] = id match {
    case DbStepPathNodeId(_, None) =>
      assert(localProvable.subgoals.size <= 1, "Node without branch only for provables with sole subgoal")
      localProvable.subgoals.headOption
    case DbStepPathNodeId(_, Some(branch)) =>
      if (localProvable.isProved) None else Some(localProvable.subgoals(branch))
  }

  /** The index of the goal (subgoal in local provable) that this node targets. */
  override def goalIdx: Int = id match {
    case DbStepPathNodeId(_, None) => 0 //@note root node
    case DbStepPathNodeId(_, Some(i)) => i
  }


  override def tacticInputSuggestions(pos: Position): Map[ArgInfo, Expression] = goal.map(g => (g, g.sub(pos))) match {
    case Some((goal, Some(subFormula))) =>
      //@HACK assumes that the currently loaded proof and this tree's proof are the same
      //      to avoid reparsing the model on every call to tacticInputSuggestions.
      val generator = TactixLibrary.invGenerator
      //@todo extend generator to generate for named arguments j(x), R, P according to tactic info
      //@HACK for loop and dG
      subFormula match {
        case Box(Loop(_), _) =>
          val invariant = generator(goal, pos)
          if (invariant.hasNext) Map(FormulaArg("j(x)") -> invariant.next)
          else Map.empty
        case Box(_: ODESystem, p) => Map(FormulaArg("P") -> p)
        case _ => Map.empty
      }
  }

  /** Deletes this node with the entire subtree underneath. */
  override def pruneBelow(): Unit = children match {
    case Nil => // nothing to do
    case (c: DbProofTreeNode)::tail =>
      assert(tail.forall(_.asInstanceOf[DbProofTreeNode].stepId == c.stepId), "Expected same step in all children")
      db.deleteExecutionStep(proofId.toInt, c.stepId.get) //@note database does cascade delete of all substeps
  }

  /** Execution step recording: predecessor step ID. */
  protected def stepId: Option[Int]
}

object DbPlainExecStepProofTreeNode {
  /** Initializes a proof tree node from a recorded execution step. The branch identifies the subgoal created by the
    * execution step. If None, the node refers to the steps source node. */
  def fromExecutionStep(db: DBAbstraction, proofId: String)(step: ExecutionStepPOJO, branch: Option[Int]): DbPlainExecStepProofTreeNode = branch match {
    case None => DbPlainExecStepProofTreeNode(db, DbStepPathNodeId(step.previousStep, Some(step.branchOrder)), proofId,
      () => {println("WARNING: ripple loading (node parent)"); db.getPlainExecutionStep(proofId.toInt, step.previousStep.get).get})
    case Some(b) => DbPlainExecStepProofTreeNode(db, DbStepPathNodeId(step.stepId, Some(b)), proofId,
      () => step)
  }
}

/** A proof tree node backed by a database of recorded execution steps. An ID Some(step),None points to the source
  * node where step was executed, an ID Some(step),Some(branch) represents a proxy for the branch subgoal created by
  * step and searches the actual successor step on demand. */
case class DbPlainExecStepProofTreeNode(db: DBAbstraction,
                                   override val id: ProofTreeNodeId, override val proofId: String,
                                   stepLoader: () => ExecutionStepPOJO) extends DbProofTreeNode(db, proofId) {
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

  /** A local provable, whose subgoals are filled in by the node's children. */
  override def localProvable: ProvableSig = dbLocalProvable

  /** The number of subgoals in the local provable (fast, doesn't actually load the provable). */
  override def numSubgoals: Int = step.numSubgoals

  /** Execution step recording: predecessor step ID (=this, when executing a tactic on this). */
  override protected def stepId: Option[Int] = id match {
    case DbStepPathNodeId(stId, _) => stId
  }

  private lazy val dbMaker = {
    println(s"Node $id: querying maker")
    db.getExecutable(step.executableId).belleExpr
  }

  private lazy val dbParent = step.previousStep match {
    case None => Some(DbRootProofTreeNode(db)(DbStepPathNodeId(None, None), proofId))
    case Some(pId) =>
      println(s"Node $id: querying parent")
      // this step knows on which branch it was executed
      val parentBranch = db.getPlainExecutionStep(proofId.toInt, stepId.get).map(_.branchOrder)
      Some(DbPlainExecStepProofTreeNode(db, DbStepPathNodeId(Some(pId), parentBranch), proofId,
        () => {println("WARNING: ripple loading (parent " + pId + ")"); db.getPlainExecutionStep(proofId.toInt, pId).get}))
  }

  private lazy val dbSubgoals = {
    println(s"Node $id: querying subgoals")
    // subgoals are the steps that have this.stepId as previousStep and this.goalIdx as branchOrder
    val successors = db.getPlainStepSuccessors(proofId.toInt, stepId.get, goalIdx)
    assert(successors.size <= 1, "Expected unique successor step for node " + id + ", but got " + successors)
    val successorSteps = successors.flatMap(s => db.getPlainExecutionStep(proofId.toInt, s.stepId.get))
    successorSteps.flatMap(s =>
      if (s.numSubgoals > 0) (0 until s.numSubgoals).map(sgi =>
        DbPlainExecStepProofTreeNode.fromExecutionStep(db, proofId)(s, Some(sgi)))
      else DbPlainExecStepProofTreeNode.fromExecutionStep(db, proofId)(s, Some(-1))::Nil
    )
  }

  private lazy val dbLocalProvable = db.getProvable(step.localProvableId.get).provable
}

/** A loaded node (root if step=None, then also parent=None, maker=None, makerShortName=None). */
case class DbLoadedProofTreeNode(db: DBAbstraction,
                                 override val id: ProofTreeNodeId, override val proofId: String,
                                 override val children: List[ProofTreeNode],
                                 step: Option[ExecutionStep]) extends DbProofTreeNode(db, proofId) {
  /** Build tree */
  children.foreach({
    case c: DbLoadedProofTreeNode => c.theParent = Some(this)
    case _ =>
  })

  /** The node's parent, None if root. */
  override def parent: Option[ProofTreeNode] = theParent

  /** The tactic (serialized BelleExpr) that produced this node from its parent. */
  override def maker: Option[String] = step.map(_ => dbMaker) //@todo load with step

  /** The tactic short name. */
  override def makerShortName: Option[String] = step.map(_.rule)

  /** A local provable, whose subgoals are filled in by the node's children. Triggers a database operation if the node's
    * step is loaded without provables. */
  override def localProvable: ProvableSig = step match {
    case None => db.getProvable(db.getProofInfo(proofId).provableId.get).provable
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

case class DbRootProofTreeNode(db: DBAbstraction)(override val id: ProofTreeNodeId, override val proofId: String) extends DbProofTreeNode(db, proofId) {
  /** The node's parent, None if root. */
  override def parent: Option[ProofTreeNode] = None

  /** The node's children. */
  override def children: List[ProofTreeNode] = theSubgoals

  /** The tactic (serialized BelleExpr) that produced this node from its parent. */
  override def maker: Option[String] = None

  /** The tactic short name. */
  override def makerShortName: Option[String] = None

  /** A local provable, whose subgoals are filled in by the node's children. */
  override def localProvable: ProvableSig = dbLocal

  /** The number of subgoals in the local provable (fast, doesn't actually load the provable). */
  override def numSubgoals: Int = 1

  /** Execution step recording: predecessor step ID. */
  override protected def stepId: Option[Int] = None

  // cached database query results
  private lazy val theSubgoals: List[ProofTreeNode] = {
    db.getFirstExecutionStep(proofId.toInt) match {
      case None => Nil
      case Some(step) =>
        val s = db.getPlainExecutionStep(proofId.toInt, step.stepId.get).get
        if (s.numSubgoals > 0) (0 until s.numSubgoals).map(sgi =>
          DbPlainExecStepProofTreeNode.fromExecutionStep(db, proofId)(s, Some(sgi))).toList
        else DbPlainExecStepProofTreeNode.fromExecutionStep(db, proofId)(s, Some(-1))::Nil
    }
  }

  private lazy val dbProofInfo = db.getProofInfo(proofId)

  private lazy val dbLocal = db.getProvable(dbProofInfo.provableId.get).provable
}

/** Builds proof trees from database-recorded step executions, starting at the specified root step (None: proof root). */
case class DbProofTree(db: DBAbstraction, override val proofId: String) extends ProofTreeBase(proofId) {
  /** Locates a node in the proof tree relative to its parent. */
  override def locate(id: ProofTreeNodeId): Option[ProofTreeNode] = id match {
    case DbStepPathNodeId(None, _) =>
      Some(DbRootProofTreeNode(db)(DbStepPathNodeId(None, None), proofId))
    case DbStepPathNodeId(Some(stepId), branch) =>
      db.getPlainExecutionStep(proofId.toInt, stepId).map(DbPlainExecStepProofTreeNode.fromExecutionStep(db, proofId)(_, branch))
  }

  /** Locates the tree root. */
  override def root: ProofTreeNode = loadedRoot match {
    case None => dbRoot
    case Some(root) => root
  }

  /** The proof's open goals */
  override def openGoals: List[ProofTreeNode] = {
    //@note alternative that loads the entire trace in case the plainOpenSteps outer join becomes slow again
//    val trace = dbTrace
//    // a final step is one that doesn't have a successor for each of its subgoals
//    val finalSteps = trace.filter(parent => trace.count(s => parent.stepId == s.previousStep) < parent.numSubgoals)
//    // final step and non-covered branches
//    val finalOpenBranches = finalSteps.map(f => f ->
//      ((0 until f.numSubgoals).toSet -- trace.filter(s => f.stepId == s.previousStep).map(_.branchOrder)).toList)

    val openSteps = dbOpenGoals
    val finalOpenBranches = openSteps.map({ case (f, closed) => f ->
      ((0 until f.numSubgoals).toSet -- closed).toList})

    val goalNodes: List[ProofTreeNode] =
      if (root.children.isEmpty && !root.done) root::Nil
      else finalOpenBranches.flatMap({ case (fs, subgoals) => subgoals.map(sgi =>
        DbPlainExecStepProofTreeNode.fromExecutionStep(db, proofId)(fs, Some(sgi))
      )})

    goalNodes
  }

  /** All proof nodes, in order of step execution. */
  override def nodes: List[ProofTreeNode] = { load(); loadedNodes }

  /** The tactic to produce this tree from its root conclusion. */
  override def tacticString: String = { load(); new ExtractTacticFromTrace(db).getTacticString(this) }

  /** Indicates whether or not the proof might be closed. */
  override def isClosed: Boolean = dbProofInfo.closed

  /** Returns a loaded proof tree to avoid ripple loading. */
  override def load(withProvables: Boolean=false): ProofTree = {
    val trace = db.getExecutionTrace(proofId.toInt, withProvables)

    // DB step is a tuple [id,previd,branch,tactic,provable,n,...]
    // which translates into n nodes (id,0,tactic,provable)...(id,n-1,tactic,provable),
    // each being a child of node (previd,branch), created by tactic
    // node (id,0)'s goal=provable.sub(0), (id,n-1)'s goal=provable.sub(n-1)

    val linkedStepNodes = trace.steps.foldRight(Map[ProofTreeNodeId, List[ProofTreeNode]]())({case (s, children) =>
      val stepResultNodes: List[ProofTreeNode] =
        if (s.subgoalsCount > 0) (0 until s.subgoalsCount).map(i =>
          DbLoadedProofTreeNode(db, DbStepPathNodeId(Some(s.stepId), Some(i)), proofId,
            children.getOrElse(DbStepPathNodeId(Some(s.stepId), Some(i)), Nil), Some(s))).toList
        else DbLoadedProofTreeNode(db, DbStepPathNodeId(Some(s.stepId), None), proofId, Nil, Some(s))::Nil // QE, close etc.

      children + (DbStepPathNodeId(s.prevStepId, Some(s.branch)) -> stepResultNodes)
    })

    loadedRoot = Some(DbLoadedProofTreeNode(db, DbStepPathNodeId(None, None), proofId,
      linkedStepNodes.getOrElse(DbStepPathNodeId(None, Some(0)), Nil), None))

    loadedNodes = loadedRoot.get :: linkedStepNodes.values.flatten.toList.sortBy(_.id match {
      case DbStepPathNodeId(stepId, branch) => (stepId, branch)
    })

    this
  }

  /** The proof info. */
  override def info: ProofPOJO = dbProofInfo

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

  private lazy val dbRoot = locate(DbStepPathNodeId(None, None)).get

  private lazy val dbTrace = db.getExecutionSteps(proofId.toInt)

  private lazy val dbOpenGoals = db.getPlainOpenSteps(proofId.toInt)

  private var loadedRoot: Option[ProofTreeNode] = None

  private var loadedNodes: List[ProofTreeNode] = Nil
}

/** Represents (one state of) an entire proof. A node in the tree represents a user-executed step. The conclusion of
  * a tree node fits its corresponding subgoal in the parent node. The conclusion of the root node is the proof
  * conclusion.
  * Created by bbohrer on 12/29/15.
  */
case class OldProofTree(proofId: String, nodes: List[TreeNode], root: TreeNode, theLeaves: List[AgendaItem]) {
  def leaves: List[AgendaItem] = theLeaves.map(item => AgendaItem(item.id, item.name, item.proofId, item.goal))

  def leavesAndRoot: List[TreeNode] = root :: leaves.map(item => item.goal)

  def findNode(id: String): Option[TreeNode] = nodes.find(node => node.id == ???/*NodeId.fromString(id)*/)

  def goalIndex(id: String): Int = { leaves.zipWithIndex.find({case (item, _) => item.id == id}).get._2 }

  def allDescendants(id: String): List[TreeNode] = {
    findNode(id).get.allDescendants
  }

  def agendaItemForNode(id: List[Int], items: List[AgendaItemPOJO]): Option[AgendaItemPOJO] = {
    ProofTree.agendaItemForNode(nodes, id, items)
  }
 }

object ProofTree {
  def agendaItemForNode(nodes: List[TreeNode], id: List[Int], items: List[AgendaItemPOJO]): Option[AgendaItemPOJO] = {
    nodes.find(_.id == id) match {
      case Some(node) =>
        var currNode: Option[List[Int]] = Some(node.id)
        while (currNode.isDefined) {
          items.find(_.initialProofNode == currNode.get) match {
            case Some(item) => return Some(item)
            case None => currNode = nodes.find(_.id == currNode.get).get.parent.map(_.id)
          }}
        None
      case None => None
    }
  }

  /** Creates a proof tree of a trace of execution steps. If the trace is incomplete, i.e., starts in the middle of
    * the actual proof, the created tree's root does not point to the actual parent in the overall tree. */
  def ofTrace(proofId: String, trace: List[ExecutionStep], rootConclusion: () => Sequent): OldProofTree = {
    val stepNodes = trace.foldLeft(Map[Int, TreeNode]())({ case (nodes, s) =>
      val nodeId = s.prevStepId match {
        case None => Nil
        case Some(prevId) => prevId :: s.branch :: Nil
      }
      val parent = s.prevStepId.flatMap(nodes.get) //@note parent==None if overall proof root, or if first elem of `trace`
      assert(parent.isEmpty || s.local.conclusion == parent.get.provable.subgoals(s.branch),
        "Inconsistent tree: conclusion of subderivation " + s.local.conclusion + " undefined or does not fit its parent " + parent.get.provable.subgoals(s.branch))
      nodes + (s.stepId -> treeNode(nodeId, s.local, parent, Some(s)))
    })
    val openGoals = stepNodes.filter({ case (_, node) =>
      node.children.size < node.provable.subgoals.size && !node.provable.isProved })
    val goalNodes =
      if (trace.isEmpty) treeNode(Nil, ProvableSig.startProof(rootConclusion()), None, None, isFake=true)::Nil
      else openGoals.flatMap({case (_, node) => node.provable.subgoals.zipWithIndex.
        filterNot({case (_, i) => node.children.exists(_.id(1) == i)}).
        map({case (sg, i) =>
          treeNode(node.startStep.get.stepId::i::Nil, ProvableSig.startProof(sg), Some(node), None, isFake=true) })})

    val finalNodes = stepNodes.values ++ goalNodes

    assert(finalNodes.count(_.parent.isEmpty) == 1, "Inconsistent tree: unique root expected, but got " + finalNodes.filter(_.parent.isEmpty))

    val items: List[AgendaItem] = goalNodes.map(goalToItem(finalNodes.toList, _, () => Nil, proofId)).toList
    OldProofTree(proofId, finalNodes.toList, finalNodes.head, items)
  }

  def ofTrace(trace:ExecutionTrace, agendaItems: () => List[AgendaItemPOJO] = () => Nil, proofFinished:Boolean = false, includeUndos:Boolean = false): OldProofTree = {
    ??? //ofTrace(trace.proofId, trace.steps, () => trace.conclusion)
  }

  private def treeNode(nodeId: List[Int], subgoal: ProvableSig, parent: Option[TreeNode], step:Option[ExecutionStep], isFake:Boolean = false): TreeNode = {
    TreeNode(nodeId, subgoal, parent, step, isFake)
  }

  private def goalToItem(allNodes: List[TreeNode], goal: TreeNode, agendaItems: () => List[AgendaItemPOJO], proofId: String):AgendaItem = {
    val item = agendaItemForNode(allNodes, goal.id, agendaItems())
    val itemName = item.map(_.displayName).getOrElse("Unnamed Goal")
    AgendaItem(???/*NodeId.toString(goal.id)*/, itemName, proofId, goal)
  }
}

// @note isFake might be completely unnecessary.
case class TreeNode (id: List[Int], provable: ProvableSig, parent: Option[TreeNode], startStep:Option[ExecutionStep], var isFake:Boolean = false) {
  assert(id.isEmpty || id.size == 2, "ID either root (Nil) or points to producing step's subgoal (stepId::subgoalIdx::Nil)")
  var endStep: Option[ExecutionStep] = None //@todo still required?
  var children: List[TreeNode] = Nil
  if (parent.nonEmpty)
    parent.get.children = parent.get.children ::: List(this)

  def allDescendants:List[TreeNode] = this :: children.flatMap(_.allDescendants)
  def rule: String = startStep.map(_.rule).getOrElse("")
}

case class AgendaItem(id: String, name: String, proofId: String, goal: TreeNode) {
  // @todo full path
  def path: List[String] = id::Nil
}

