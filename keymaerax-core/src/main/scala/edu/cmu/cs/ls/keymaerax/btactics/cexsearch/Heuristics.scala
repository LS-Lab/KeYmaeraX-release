package edu.cmu.cs.ls.keymaerax.btactics.cexsearch

import edu.cmu.cs.ls.keymaerax.core.{Formula, StaticSemantics}

/**
  * Created by bbohrer on 4/24/16.
  */
object Heuristics {
  def QECost(fml:Formula):Double = {
    val factor = 1.0
    val semantics = StaticSemantics(fml)
    val vars = (semantics.bv ++ semantics.fv).toSet
    val cost = Math.pow(2.0, Math.pow(2.0, vars.size))
    cost * factor
  }
}
