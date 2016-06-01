package edu.cmu.cs.ls.keymaerax.hydra

import _root_.edu.cmu.cs.ls.keymaerax.btactics.Augmentors
import _root_.edu.cmu.cs.ls.keymaerax.core.{Formula, ProverException, Sequent}
import _root_.edu.cmu.cs.ls.keymaerax.parser.StringConverter

import scala.collection.immutable.Nil
import scala.collection.immutable

/** Represents (one state of) an entire proof.
  * A ProofTree can contain steps that are inserted automatically by HyDRA for its own purposes (namely undo) in addition
  * to steps executed by a user.
  * Created by bbohrer on 12/29/15.
  */
case class ProofTree(proofId: String, nodes: List[TreeNode], root: TreeNode, theLeaves: List[AgendaItem]) {
  def leaves =
    theLeaves.map{case item =>
      AgendaItem(item.id, item.name, item.proofId, item.goal)
    }

  def leavesAndRoot = root :: leaves.map({case item => item.goal})

  def findNode(id: String) = nodes.find({case node =>
    node.id.toString == id})

  def goalIndex(id: String): Int = {
    leaves.zipWithIndex.find({case (item, i) => item.id == id}).get._2
  }

  def allDescendants(id: String): List[TreeNode] = {
    findNode(id).get.allDescendants
  }

  def agendaItemForNode(id: String, items: List[AgendaItemPOJO]): Option[AgendaItemPOJO] = {
    ProofTree.agendaItemForNode(nodes, id, items)
  }
 }

object ProofTree {
  def agendaItemForNode(nodes: List[TreeNode], id: String, items: List[AgendaItemPOJO]): Option[AgendaItemPOJO] = {
    nodes.find(_.id == id.toInt) match {
      case Some(node) =>
        var currNode:Option[Int] = Some(node.id)
        while (currNode.isDefined) {
          items.find({case item => item.initialProofNode == currNode.get}) match {
            case Some(item) => return Some(item)
            case None => currNode = nodes.find(_.id == currNode.get).get.parent.map(_.id)
          }}
        None
      case None => None
    }
  }

  def ofTrace(trace:ExecutionTrace, agendaItems: List[AgendaItemPOJO] = Nil, proofFinished:Boolean = false, includeUndos:Boolean = false): ProofTree = {
    var currentNodeId = 1

    def treeNode(subgoal: Sequent, parent: Option[TreeNode], step:Option[ExecutionStep], isFake:Boolean = false): TreeNode = {
      val nodeId = currentNodeId
      currentNodeId = currentNodeId + 1
      TreeNode(nodeId, subgoal, parent, step, isFake)
    }

    def goalToItem(allNodes: List[TreeNode], goal: TreeNode):AgendaItem = {
      val item = agendaItemForNode(allNodes, goal.id.toString, agendaItems)
      val itemName = item.map(_.displayName).getOrElse("Unnamed Goal")
      AgendaItem(goal.id.toString, itemName, trace.proofId, goal)
    }

    if (trace.steps.isEmpty) {
      val sequent = trace.conclusion
      val node = treeNode(sequent, None, None)
      val item = goalToItem(List(node), node)
      return ProofTree(trace.proofId, List(node), node, List(item))
    }

    val inputProvable = trace.steps.head.input
    var openGoals = inputProvable.subgoals.map({case subgoal => treeNode(subgoal, None, None)})
    var allNodes = openGoals.toList
    var steps = trace.steps
    while (steps.nonEmpty && steps.head.output.nonEmpty) {
      val step = steps.head
      val branch = step.branch
      val outputProvable = step.output.get
      openGoals(branch).endStep = Some(step)
      /* This step closed a branch*/
      if(outputProvable.subgoals.length == openGoals.length - 1) {
        openGoals = openGoals.slice(0, branch) ++ openGoals.slice(branch + 1, openGoals.length)
      } else {
        val delta =
          outputProvable.subgoals
            .zipWithIndex.filter({case (sg,i) => i >= openGoals.length || openGoals(i).sequent != sg})
            .map(_._1)
        if (delta.nonEmpty) {
          val updatedNode = treeNode(delta.head, Some(openGoals(branch)), Some(step))
          val addedNodes = delta.tail.map({ case sg => treeNode(sg, Some(openGoals(branch)), Some(step)) })
          openGoals = openGoals.updated(branch, updatedNode) ++ addedNodes
          allNodes = allNodes ++ (updatedNode :: addedNodes.toList)
        } else if (!step.isUserExecuted && !includeUndos) {
          /* Ensure that node ID's are consistent between versions of the tree that do or do not contain undo nodes
          * by generating the same ID's in both cases.*/
          currentNodeId = currentNodeId + 1
        }
        else {
          val isFake = !step.isUserExecuted
          val updatedNode = treeNode(openGoals(branch).sequent, Some(openGoals(branch)), Some(step), isFake)
          openGoals = openGoals.updated(branch, updatedNode)
          allNodes = allNodes :+ updatedNode
        }
      }
      steps = steps.tail
    }
    import StringConverter._
    val (finalNodes, goalNodes) =
      if(!proofFinished) {
        (allNodes, openGoals)
      } else {
        /* Add nodes to indicate that all the leaves have been closed, then return the new leaves as our agenda so every
          branch is visible. Since we have to display a sequent, use  |- true to let the user know the branch is closed. */
        val goals = allNodes.filter(_.children.isEmpty)
        val newNodes = goals.map{case goal =>
            treeNode(Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("true".asFormula)),
              Some(goal), goal.endStep)}
        (allNodes ++ newNodes, newNodes)
      }

    val items: List[AgendaItem] = goalNodes.map(goalToItem (finalNodes, _)).toList
    ProofTree(trace.proofId, finalNodes, finalNodes.head, items)
  }
}

// @note isFake might be completely unnecessary.
case class TreeNode (id: Int, sequent: Sequent, parent: Option[TreeNode], startStep:Option[ExecutionStep], var isFake:Boolean = false) {
  var endStep: Option[ExecutionStep] = None
  var children: List[TreeNode] = Nil
  if (parent.nonEmpty)
    parent.get.children = this :: parent.get.children

  def allDescendants:List[TreeNode] = this :: children.flatMap{case child => child.allDescendants}
  def rule:String = { startStep.map{case step => step.rule}.getOrElse("")}
}

case class AgendaItem(id: String, name: String, proofId: String, goal: TreeNode) {
  // @todo full path
  def path = List(goal.id.toString)
}

