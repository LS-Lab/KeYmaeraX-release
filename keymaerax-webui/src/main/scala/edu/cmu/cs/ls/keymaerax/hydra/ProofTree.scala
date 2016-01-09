package edu.cmu.cs.ls.keymaerax.hydra

import _root_.edu.cmu.cs.ls.keymaerax.core.{ProverException, Sequent}

import scala.collection.immutable.Nil

/**
  * Created by bbohrer on 12/29/15.
  */
case class ProofTree(proofId: String, nodes: List[TreeNode], root: TreeNode, theLeaves: List[AgendaItem]) {
  def leaves =
    theLeaves.map{case item =>
      // @note Item id and goal id are secretly the same, need to keep them in sync.
      val realId = (findNode(item.id).get).id.toString
      AgendaItem(item.id, item.name, item.proofId, item.goal.real())
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

  def ofTrace(trace:ExecutionTrace, agendaItems: List[AgendaItemPOJO] = Nil): ProofTree = {
    var currentNodeId = 1

    def treeNode(subgoal: Sequent, parent: Option[TreeNode], step:Option[ExecutionStep], isFake:Boolean = false): TreeNode = {
      val nodeId = currentNodeId
      currentNodeId = currentNodeId + 1
      TreeNode(nodeId, subgoal, parent, step, isFake)
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
        if (delta.nonEmpty) {
          openGoals(branch).endStep = Some(step)
          val updatedNode = treeNode(delta.head, Some(openGoals(branch)), Some(step))
          val addedNodes = delta.tail.map({ case sg => treeNode(sg, Some(openGoals(branch)), Some(step)) })
          openGoals = openGoals.updated(branch, updatedNode) ++ addedNodes
          allNodes = allNodes ++ (updatedNode :: addedNodes.toList)
        } else  {
          val isFake = !step.isUserExecuted
          openGoals(branch).endStep = Some(step)
          val updatedNode = treeNode(openGoals(branch).sequent, Some(openGoals(branch)), Some(step), isFake)
          openGoals = openGoals.updated(branch, updatedNode)
          allNodes = allNodes :+ updatedNode
        }
      }
      steps = steps.tail
    }
    val items: List[AgendaItem] = openGoals.map({case i =>
      val item = agendaItemForNode(allNodes, i.id.toString, agendaItems)
      val itemName = item.map(_.displayName).getOrElse("Unnamed Goal")
      AgendaItem(i.id.toString, itemName, trace.proofId, i)}).toList
    ProofTree(trace.proofId, allNodes, allNodes.head, items)
  }
}

case class TreeNode (id: Int, sequent: Sequent, theParent: Option[TreeNode], startStep:Option[ExecutionStep], var isFake:Boolean = false) {
  var theChildren: List[TreeNode] = Nil
  var endStep: Option[ExecutionStep] = None
  if (parent.nonEmpty)
    parent.get.theChildren = this :: parent.get.theChildren

  def real(searchUpward:Boolean = false): TreeNode = {
    if (isFake) {
      if (searchUpward)
        theChildren.head.real(searchUpward)
      else
        theParent.get.real(searchUpward)
    }
    else
      this
  }


  def parent: Option[TreeNode] = real().theParent.map(_.real())

  def children = theChildren.flatMap{case child =>
    try {
      List(child.real(searchUpward = true))
    } catch {
      case _:NoSuchElementException => Nil
    }}

  def allDescendants:List[TreeNode] = this :: theChildren.flatMap{case child => child.allDescendants}
  def rule:String = { startStep.map{case step => step.rule}.getOrElse("")}
}

case class AgendaItem(id: String, name: String, proofId: String, goal: TreeNode) {
  // @todo full path
  def path = List(goal.id.toString)
}

