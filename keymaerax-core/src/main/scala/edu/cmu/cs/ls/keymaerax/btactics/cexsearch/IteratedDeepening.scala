package edu.cmu.cs.ls.keymaerax.btactics.cexsearch

/**
  * Created by hgommers on 4/27/2016.
  */
class IteratedDeepening extends (SearchNode => Option[ConcreteState]) {

    def apply(node:SearchNode):Option[ConcreteState] = {

      var currDepth = 0
       while (true) {
        val dfs:BoundedDFS = new BoundedDFS(currDepth + 1)
        val found:Option[ConcreteState] = dfs(node)

        found match {
          case None => currDepth = currDepth + 1
          case Some(g) => return Some(g)
        }
      }
      /* If we ever exit the loop something is wrong*/
      ???
    }
}

