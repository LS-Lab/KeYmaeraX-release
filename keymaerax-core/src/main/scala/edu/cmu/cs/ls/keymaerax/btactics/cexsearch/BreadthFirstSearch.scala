package edu.cmu.cs.ls.keymaerax.btactics.cexsearch

/**
  * @TODO Bounded-depth search, Iterative-deepening, A*, IDA*
  * Created by bbohrer on 4/24/16.
  */
object BreadthFirstSearch extends (SearchNode => Option[ConcreteState]) {
  def bfs(frontier:Set[SearchNode], visited:Set[SearchNode]):Option[ConcreteState] = {
    val (goalReached, _) = frontier.map({case sn => sn.goal}).partition({case result => result.isDefined})
    (frontier.size, goalReached.toList) match {
      case (_, Some(firstGoal)::_) => Some(firstGoal)
      case (0, _) => None
      case _ =>
        val nextLevel = frontier.toList.map({case sn => sn.children}).fold(Set.empty)({case (s1, s2) => s1 | s2})
        bfs(nextLevel.diff(visited), visited | frontier)
    }
  }

  def apply(node:SearchNode) = bfs(Set(node), Set.empty)
}
