package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon._
import BelleOpSpec.op
import edu.cmu.cs.ls.keymaerax.btactics.TacticInfo
import edu.cmu.cs.ls.keymaerax.core.{Equal, Expression, Formula, Term}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter

import scala.util.Try

/**
  * A pretty-printer for the Bellerophon tactics language.
  *
  * @author Nathan Fulton
  * @note Prefer this implementation over [[BelleExpr.prettyString]].
  */
object BellePrettyPrinter extends (BelleExpr => String) {
  override def apply(e: BelleExpr): String = pp(e, 0)

  private def pp(e : BelleExpr, indent: Int): String = {
    // Prefer the code name if one exists for this tactic, but looking up code name may throw exception.
    //      println("Looking for a code name for " + e)
    Try(TacticInfo.apply(e.prettyString)).toOption match {
      // anything that needs a generator (e.g. master) will never be a BelleExpr so might as well take the codeName
      // directly for those.
      case Some(info) if info.belleExpr == e || info.needsGenerator => info.codeName
      case _ => e match {
        case DefTactic(name, t) => op(e).terminal.img + " " + name + " " + AS.img + " (" + pp(t, indent) + ")"
        case ApplyDefTactic(DefTactic(name, _)) => name
        case SeqTactic(l,r)     => wrapLeft(e, l, indent) + " " + op(e).terminal.img + " " + wrapRight(e, r, indent)
        case EitherTactic(l,r) => wrapLeft(e, l, indent) + " " + op(e).terminal.img + " " + wrapRight(e, r, indent)
        case BranchTactic(ts) => op(e).terminal.img +
          "(" + newline(indent) + ts.map(pp(_, indent+1)).mkString(", " + newline(indent+1)) + newline(indent) + ")"
        case SaturateTactic(t) => wrapLeft(e, t, indent) + op(e).terminal.img
        case it : StringInputTactic =>
          val eargs = it.inputs.map(input => argPrinter(Left(input))).mkString(", ")
          it.name + "(" + eargs + ")"
        case b : BuiltInTactic => b.name
        case b: BuiltInPositionTactic => b.name
        case b: BuiltInLeftTactic => b.name
        case b: BuiltInRightTactic => b.name
        case e: PartialTactic => wrapLeft(e, e.child, indent) + " " + op(e).terminal.img
        case e: RepeatTactic => wrapLeft(e, e.child, indent) + op(e).terminal.img
        case OnAll(c) => op(e).terminal.img + "(" + pp(c, indent) + ")"
        case Let(abbr, value, inner) => op(e).terminal.img + " (" + argPrinter(Left(
          (abbr, value) match {
            case (a: Term, v: Term) => Equal(a, v)
            case (a: Formula, v: Formula) => edu.cmu.cs.ls.keymaerax.core.Equiv(a, v)
          })) + ") " + IN.img + " (" +
          newline(indent+1) + pp(inner, indent+1) + newline(indent) + ")"
        case DependentPositionTactic(name) => name // name of a DependentPositionTactic is the codeName
        case adp: AppliedDependentPositionTactic => adp.pt match {
          case e: DependentPositionWithAppliedInputTactic =>
            val eargs = e.inputs.map(input => argPrinter(Left(input))).mkString(", ")
            val sep = if (e.inputs.isEmpty) "" else ", "
            e.name + "(" + eargs + sep + argPrinter(Right(adp.locator)) + ")"
          case e: DependentPositionTactic => e.name + "(" + argPrinter(Right(adp.locator)) + ")" //@todo not sure about this.
        }
        case ap : AppliedPositionTactic => pp(ap.positionTactic, indent) + argListPrinter(Right(ap.locator) :: Nil)
        case it : InputTactic =>
          val eargs = it.inputs.map(input => argPrinter(Left(input))).mkString(", ")
          it.name + "(" + eargs + ")"
        case ProveAs(_, _, _) => "proveAs"
        case t: AppliedBuiltinTwoPositionTactic => t.positionTactic.name + "(" + t.posOne.prettyString + ", " + t.posTwo.prettyString + ")"
        case NamedTactic(name, _) if name != "ANON" => name
        case dot: BelleDot => "_@" + dot.hashCode()
        case DependentTactic(name) => name // must be last, otherwise applied dependent tactics lose their position
        case _ => throw PrinterException(s"Do not know how to pretty-print $e")
      }
    }
  }

  private def argListPrinter(args : List[BelleParser.TacticArg]) = {
    "(" + args.map(argPrinter).reduce(_ + ", " + _) + ")"
  }

  private def argPrinter(arg : BelleParser.TacticArg) = arg match {
    case Left(expr: Expression) => "{`" + KeYmaeraXPrettyPrinter(expr) + "`}"
    case Left(expr: String) => "{`" + expr + "`}"
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
