package edu.cmu.cs.ls.keymaerax.btacticinterface

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.btactics.Idioms
import edu.cmu.cs.ls.keymaerax.core.{SeqPos, Formula}

/**
  * Constructs a [[edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr]] from a name of the form ``object.method``
  * @author Nathan Fulton
  */
object ReflectiveExpressionBuilder {
  def apply(name: String) : BelleExpr =
    BTacticNamesTable.reservedNames.get(name) match {
      case Some(e) => e
      case None    => ???
    }


  def apply(name: String, arguments: List[Either[Formula, SeqPos]]) : BelleExpr =
    BTacticNamesTable.reservedNames.get(name) match {
      case Some(e) => e
      case None    => ???
    }

  /**
    * Contains default names.
    * @author Nathan Fulton
    */
  private object BTacticNamesTable {
    val reservedNames : Map[String, BelleExpr] = Map(
      "nil" -> Idioms.nil
    )
  }
}


