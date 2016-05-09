package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.{core, bellerophon}
import edu.cmu.cs.ls.keymaerax.bellerophon._
import BelleOpSpec.op
import edu.cmu.cs.ls.keymaerax.btactics.TacticInfo
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter

/**
  * A pretty-printer for the Bellerophon tactics language.
  *
  * @author Nathan Fulton
  * @note Prefer this implementation over [[BelleExpr.prettyString]].
  */
object BellePrettyPrinter extends (BelleExpr => String) {
  override def apply(e: BelleExpr): String = pp(e, 0)

  private def pp(e : BelleExpr, indent: Int): String = {
    try {
      //Prefer the code name if one exists for this tactic.
//      println("Looking for a code name for " + e)
      val info = TacticInfo.apply(e.prettyString)
      if(info.belleExpr.asInstanceOf[BelleExpr] != e) throw new Exception("")
      else info.codeName
    }
    catch {
      case exn:Throwable =>
        e match {
          case SeqTactic(l,r)     => wrapLeft(e, l, indent) + " " + op(e).terminal.img + " " + wrapRight(e, r, indent)
          case EitherTactic(l,r) => wrapLeft(e, l, indent) + " " + op(e).terminal.img + " " + wrapRight(e, r, indent)
          case BranchTactic(ts) => op(e).terminal.img +
            "(" + newline(indent) + ts.map(pp(_, indent+1)).mkString(", " + newline(indent+1)) + newline(indent) + ")"
          case SaturateTactic(t, a) => "(" + pp(t, indent) + ")" + op(e).terminal.img
          case b : BuiltInTactic => b.name
          case e: PartialTactic => op(e).terminal.img + "(" + pp(e.child, indent) + ")"
          case e: RepeatTactic => "(" + pp(e.child, indent) + ")^" + e.times
          case adp: AppliedDependentPositionTactic => adp.pt match {
            case e: DependentPositionWithAppliedInputTactic => e.name + "({`" + argPrinter(Left(e.input)) + "`}, " + argPrinter(Right(adp.locator)) + ")"
            case e: DependentPositionTactic => e.name + "(" + argPrinter(Right(adp.locator)) + ")" //@todo not sure about this.
          }
          case ap : AppliedPositionTactic => pp(ap.positionTactic, indent) + argListPrinter(Right(ap.locator) :: Nil)
          case it : InputTactic[_] => {
            val theArg = it.input match {
              case e : core.Expression => Left(e)
              case _ => throw PrinterException("Cannot print input tactics that take non-expressions as input.") //@todo that class probably just shouldn't even be generic now that we have DependentPositionTactics etc.
            }

            it.name + "(" + argPrinter(theArg) + ")"
          }
          case _ => throw PrinterException(s"Do not no how to pretty-print ${e}")
        }
    }
  }

  private def argListPrinter(args : List[BelleParser.TacticArg]) = {
    "(" + args.map(argPrinter).reduce(_ + ", " + _) + ")"
  }

  private def argPrinter(arg : BelleParser.TacticArg) = arg match {
    case Left(expr) => "{`" + KeYmaeraXPrettyPrinter(expr) + "`}"
    case Right(loc) => loc.prettyString
  }

  private val TAB = "  "
  private def newline(indent: Int) = {
    var s : String = "\n"
    for(i <- 1 until indent) {
      s = s + TAB
    }
    s
  }

  private def wrapLeft(parent: BelleExpr, current: BelleExpr, indent: Int) : String =
    if(op(parent) < op(current) || (op(parent) == op(current) && !op(current).leftAssoc))
      wrap(current, indent)
    else
      pp(current, indent)

  private def wrapRight(parent: BelleExpr, current: BelleExpr, indent: Int) : String =
    if(op(parent) < op(current) || (op(parent) == op(current) && op(current).leftAssoc))
      wrap(current, indent)
    else
      pp(current, indent)

  private def wrap(e : BelleExpr, indent: Int) = "(" + pp(e, indent) + ")"
}


case class PrinterException(msg: String) extends Exception(msg)
