package edu.cmu.cs.ls.keymaerax.btacticinterface

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.{Fixed, ExposedTacticsLibrary}
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

  def apply(name: String, arguments: List[Either[Formula, SeqPos]]) : BelleExpr = {
    val theTactic =
      ExposedTacticsLibrary.tactics.get(name) match {
        case Some(e) => e
        case None => ??? //@todo implement the class.method builder.
      }

    //Positional tactics.
    if(theTactic.isInstanceOf[PositionalTactic] && arguments.forall(p => p.isRight) && arguments.length == 1) {
      AppliedPositionTactic(theTactic.asInstanceOf[PositionalTactic], Fixed(arguments.head.right.get))
    }
    else {
      ??? //Not sure how to parser stuff with formulas yet.
    }
  }
}

