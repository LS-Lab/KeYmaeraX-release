package edu.cmu.cs.ls.keymaerax.btacticinterface

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.btactics.ExposedTacticsLibrary
import edu.cmu.cs.ls.keymaerax.core.{SeqPos, Formula}

/**
  * Constructs a [[edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr]] from a name of the form ``object.method``
  * @author Nathan Fulton
  */
object ReflectiveExpressionBuilder {
  def apply(name: String) : BelleExpr =
    ExposedTacticsLibrary.tactics.get(name) match {
      case Some(e) => e
      case None    => ??? //@todo implement the class.method builder.
    }

  def apply(name: String, arguments: List[Either[Formula, SeqPos]]) : BelleExpr =
    ExposedTacticsLibrary.tactics.get(name) match {
      case Some(e) => e
      case None    => ??? //@todo implement the class.method builder.
    }
}

