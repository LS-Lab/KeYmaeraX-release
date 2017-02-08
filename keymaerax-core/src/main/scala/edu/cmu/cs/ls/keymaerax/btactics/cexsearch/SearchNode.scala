package edu.cmu.cs.ls.keymaerax.btactics.cexsearch

/**
  * Created by bbohrer on 4/24/16.
  */
trait SearchNode {
  def goal: Option[ConcreteState]
  def value: Float
  def children:Set[SearchNode]
}
