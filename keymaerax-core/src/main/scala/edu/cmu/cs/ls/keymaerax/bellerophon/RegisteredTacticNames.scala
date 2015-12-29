package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.Idioms

/**
  * Contains default names.
  * @author Nathan Fulton
  */
object RegisteredTacticNames {
  var registeredNames : BiMap[String, BelleExpr] = new BiMap(Map(
    "nil" -> Idioms.nil
  ))

  def register(name: String, tactic: BelleExpr) = {
    registeredNames = registeredNames + ((name, tactic))
  }
}
