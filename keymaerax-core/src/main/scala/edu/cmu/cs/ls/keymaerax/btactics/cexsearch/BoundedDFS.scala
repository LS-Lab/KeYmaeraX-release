package edu.cmu.cs.ls.keymaerax.btactics.cexsearch

/**
  * Created by hgommers on 4/27/2016.
  */
class BoundedDFS (maxDepth: Int) extends (SearchNode => Option[ConcreteState]) {
  def dfs (frontier: List[(SearchNode,Int)], currNode:SearchNode, currDepth: Int, maxDepth: Int) : Option[ConcreteState] = {
    def next = {
      frontier match {
        case Nil => None
        case ((n,d) :: xs) => dfs(xs, n, d, maxDepth)
      }
    }
    if (currDepth > maxDepth) next
    else {
      currNode.goal match {
        case None =>
          currNode.children.toList match {
            case Nil => next
            case littles => dfs(List.concat(frontier, littles.tail.map((_, currDepth+1))),  littles.head, currDepth + 1, maxDepth)
          }
        case (Some(g)) => Some(g)
      }
    }
  }

  def apply(node:SearchNode):Option[ConcreteState] = dfs(List((node,0)), node, 0, maxDepth)
}
