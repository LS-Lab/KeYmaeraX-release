package edu.cmu.cs.ls.keymaerax.btactics.cexsearch

/**
  * Created by hgommers on 4/27/2016.
  */
class BoundedDFS (maxDepth: Int) extends (SearchNode => Option[ConcreteState]) {
  def dfs (frontier: List[SearchNode], visited: Set[SearchNode], currNode:SearchNode, currDepth:Int, maxDepth: Int) : Option[ConcreteState] = {
    if (currDepth > maxDepth) None
    else {
      currNode.goal match {
        case None => val littles = currNode.children.toList
          dfs(List.concat(frontier, littles.tail), visited + currNode, currNode.children.toList.head, currDepth + 1, maxDepth)
        case (Some(g)) => Some(g)
      }
    }
  }

  def apply(node:SearchNode):Option[ConcreteState] = dfs(List(node), Set.empty, node, 0, maxDepth)
}
