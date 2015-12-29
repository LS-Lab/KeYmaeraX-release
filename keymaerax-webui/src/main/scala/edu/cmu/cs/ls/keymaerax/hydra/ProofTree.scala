package edu.cmu.cs.ls.keymaerax.hydra

import _root_.edu.cmu.cs.ls.keymaerax.core.Sequent

import scala.collection.immutable.Nil

/**
  * Created by bbohrer on 12/29/15.
  */
case class ProofTree(id: String, nodes: List[TreeNode], root: TreeNode, leaves: List[AgendaItem]) {
  def leavesAndRoot = root :: leaves.map({case item => item.goal})
  def parent(id: String): Option[TreeNode] =
    nodes.find({case node => node.id.toString == id}).flatMap({case node => node.parent})
  def findNode(id: String) = nodes.find({case node => node.id.toString.equals(id)})
}
object ProofTree {
  def ofTrace(trace:ExecutionTrace): ProofTree = {
    var currentNodeId = 1

    def treeNode(subgoal: Sequent, parent: Option[TreeNode]): TreeNode = {
      val nodeId = currentNodeId
      currentNodeId = currentNodeId + 1
      TreeNode(nodeId, subgoal, parent)
    }

    if (trace.steps.isEmpty) {
      val sequent = trace.conclusion
      val node = treeNode(sequent, None)
      return ProofTree(trace.proofId, List(node), node, List(AgendaItem("0", "Unnamed Item", trace.toString, node)))
    }

    val ProvableSequents(conclusion, rootSubgoals) = trace.steps.head.input
    var openGoals = rootSubgoals.map({case subgoal => treeNode(subgoal, None)})
    var allNodes = openGoals
    var steps = trace.steps
    while (steps.nonEmpty && steps.head.output.nonEmpty) {
      val step = steps.head
      val branch = step.branch.left.get
      val ProvableSequents(_, endSubgoals) = step.output.get
      /* This step closed a branch*/
      if(endSubgoals.length == openGoals.length - 1) {
        openGoals = openGoals.slice(0, branch) ++ openGoals.slice(branch + 1, openGoals.length)
      } else {
        val (updated :: added) =
          endSubgoals.filter({case sg => !openGoals.exists({case node => node.sequent == sg})})
        val updatedNode = treeNode(updated, Some(openGoals(branch)))
        val addedNodes = added.map({case sg => treeNode(sg, Some(openGoals(branch)))})
        openGoals = openGoals.updated(branch, updatedNode) ++ addedNodes
        allNodes = allNodes ++ (updatedNode :: addedNodes)
      }
      steps = steps.tail
    }
    var items:List[AgendaItem] = Nil
    for (i <- openGoals.indices) {
      items = AgendaItem(i.toString, "Unnamed Goal", trace.proofId, openGoals(i)) :: items
    }
    ProofTree(trace.proofId, allNodes, allNodes.head, items.reverse)
  }
}

case class TreeNode (id: Int, sequent: Sequent, parent: Option[TreeNode]) {
  var children: List[TreeNode] = Nil
  if (parent.nonEmpty)
    parent.get.children = this :: parent.get.children
  def rule = "Unimplemented"
}

case class AgendaItem(id: String, name: String, proofId: String, goal: TreeNode) {
  // @todo full path
  def path = List(goal.id.toString)
}

