package edu.cmu.cs.ls.keymaerax.hydra

import edu.cmu.cs.ls.keymaerax.bellerophon._
import org.apache.logging.log4j.scala.Logging

/**
  * @note stub! At the moment just trying things out.
  * Created by nfulton on 12/22/15.
  */
class DatabaseTacticSerializer(db: DBAbstraction) extends IOListener with Logging {
  var ignoreUntilAfter : Option[BelleExpr] = None

  edu.cmu.cs.ls.keymaerax.core.PrettyPrinter.setPrinter(edu.cmu.cs.ls.keymaerax.parser.FullPrettyPrinter)
  def begin(input: BelleValue, expr: BelleExpr): Unit = {
    if (ignoreUntilAfter.isEmpty) {
      expr match {
        case t: InputTactic => {
          print(t.prettyString)
          ignoreUntilAfter = Some(expr)
        }
        case t: InputTactic => logger.warn("Don't know what to do with InputTactics that don't take Formulas.")
        case PartialTactic(t, _) => print("partial(")
      }
    }
  }

  def end(input: BelleValue, expr: BelleExpr, output: Either[BelleValue,BelleThrowable]): Unit = {
    if (ignoreUntilAfter.isEmpty) {
      expr match {
          //@todo print(l + ")")???
        case PartialTactic(t, l) => print(")")
        case t : InputTactic => //nothing.
      }
    }
    else if (ignoreUntilAfter.nonEmpty && ignoreUntilAfter.get == expr) {
      ignoreUntilAfter = None
    }
  }

  def kill(): Unit = {}
}
