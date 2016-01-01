package edu.cmu.cs.ls.keymaerax.hydra

import _root_.edu.cmu.cs.ls.keymaerax.core.Sequent

import scala.collection.immutable.Nil

/**
  * Created by bbohrer on 12/29/15.
  */
case class ProofTree(proofId: String, nodes: List[TreeNode], root: TreeNode, leaves: List[AgendaItem]) {
  def leavesAndRoot = root :: leaves.map({case item => item.goal})

  def parent(id: String): Option[TreeNode] =
    nodes.find({case node => node.id.toString == id}).flatMap({case node => node.parent})

  def findNode(id: String) = nodes.find({case node =>
    node.id.toString == id})

  def goalIndex(id: String): Int = {
    leaves.zipWithIndex.find({case (item, i) => item.id == id}).get._2
  }

  def allDescendants(id: String): List[TreeNode] = {
    findNode(id).get.allDescendants
  }
 }
object ProofTree {
  def ofTrace(trace:ExecutionTrace): ProofTree = {
    var currentNodeId = 1

    def treeNode(subgoal: Sequent, parent: Option[TreeNode], step:Option[ExecutionStep]): TreeNode = {
      val nodeId = currentNodeId
      currentNodeId = currentNodeId + 1
      TreeNode(nodeId, subgoal, parent, step)
    }

    if (trace.steps.isEmpty) {
      val sequent = trace.conclusion
      val node = treeNode(sequent, None, None)
      return ProofTree(trace.proofId, List(node), node, List(AgendaItem(node.id.toString, "Unnamed Item", trace.proofId, node)))
    }

    val inputProvable = trace.steps.head.input
    var openGoals = inputProvable.subgoals.map({case subgoal => treeNode(subgoal, None, Some(trace.steps.head))})
    var allNodes = openGoals.toList
    var steps = trace.steps
    while (steps.nonEmpty && steps.head.output.nonEmpty) {
      val step = steps.head
      val branch = step.branch
      val outputProvable = step.output.get
      /* This step closed a branch*/
      if(outputProvable.subgoals.length == openGoals.length - 1) {
        openGoals = openGoals.slice(0, branch) ++ openGoals.slice(branch + 1, openGoals.length)
      } else {
        val delta =
          outputProvable.subgoals.filter({case sg => !openGoals.exists({case node => node.sequent == sg})})
        openGoals(branch).endStep = Some(step)
        val updatedNode = treeNode(delta.head, Some(openGoals(branch)), Some(step))
        val addedNodes = delta.tail.map({case sg => treeNode(sg, Some(openGoals(branch)), Some(step))})
        openGoals = openGoals.updated(branch, updatedNode) ++ addedNodes
        allNodes = allNodes ++ (updatedNode :: addedNodes.toList)
      }
      steps = steps.tail
    }
    val items: List[AgendaItem] = openGoals.map(i => AgendaItem(i.id.toString, "Unnamed Goal", trace.proofId, i)).toList
    ProofTree(trace.proofId, allNodes, allNodes.head, items)
  }
}

case class TreeNode (id: Int, sequent: Sequent, parent: Option[TreeNode], startStep:Option[ExecutionStep]) {
  var children: List[TreeNode] = Nil
  var endStep: Option[ExecutionStep] = None
  if (parent.nonEmpty)
    parent.get.children = this :: parent.get.children
  def rule = "Unimplemented"
  def allDescendants:List[TreeNode] = this :: children.flatMap{case child => child.allDescendants}
}

case class AgendaItem(id: String, name: String, proofId: String, goal: TreeNode) {
  // @todo full path
  def path = List(goal.id.toString)
}

