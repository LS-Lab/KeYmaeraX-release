package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.core.{Expression, Formula}

/**
  * @note stub! At the moment just trying things out.
  * Created by nfulton on 12/22/15.
  */
class DatabaseTacticSerializer(db: DBAbstraction) extends IOListener {
  var ignoreUntilAfter : Option[BelleExpr] = None

  edu.cmu.cs.ls.keymaerax.core.PrettyPrinter.setPrinter(edu.cmu.cs.ls.keymaerax.parser.FullPrettyPrinter)
  def begin(input: BelleValue, expr: BelleExpr): Unit = {
    if (ignoreUntilAfter.isEmpty) {
      expr match {
        case t: InputTactic[Formula] => {
          print(t.prettyString)
          ignoreUntilAfter = Some(expr)
        }
        case t: InputTactic[_] => println("Don't know what to do with InputTactics that don't take Formulas.")
        case PartialTactic(t) => print("partial(")
      }
    }
  }

  def end(input: BelleValue, expr: BelleExpr, output: BelleValue): Unit = {
    if (ignoreUntilAfter.isEmpty) {
      expr match {
        case PartialTactic(t) => print(")")
        case t : InputTactic[_] => //nothing.
      }
    }
    else if (ignoreUntilAfter.nonEmpty && ignoreUntilAfter.get == expr) {
      ignoreUntilAfter = None
    }
  }

  def kill(): Unit = {}
}
