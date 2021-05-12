package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon._
import BelleOpSpec.op
import edu.cmu.cs.ls.keymaerax.btactics.macros.{GeneratorArg, TacticInfo}
import edu.cmu.cs.ls.keymaerax.core.{Equal, Expression, Formula, Term}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.btactics.macros.DerivationInfoAugmentors._
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr

import scala.util.Try

/**
  * A pretty-printer for the Bellerophon tactics language.
  *
  * @author Nathan Fulton
  * @note Prefer this implementation over [[BelleExpr.prettyString]].
  */
object BellePrettyPrinter extends (BelleExpr => String) {
  override def apply(e: BelleExpr): String = pp(e, 0)

  private def sanitizeUnary(t: String, op: String): String = t match {
    case "" | "()" => ""
    case _ => t + op
  }

  private def sanitizeBinary(left: String, op: String, right: String, sep: String = " "): String = left match {
    case "" | "()" => right match {
      case "" | "()" => ""
      case _ => right
    }
    case _ => right match {
      case "" | "()" => left
      case _ => left + sep + op + sep + right
    }
  }

  private def pp(e: BelleExpr, indent: Int): String = {
    // Prefer the code name if one exists for this tactic, but looking up code name may throw exception.
    //      println("Looking for a code name for " + e)
    Try(TacticInfo.apply(e.prettyString)).toOption match {
      // anything that needs a generator (e.g. master) will never be a BelleExpr so might as well take the codeName
      // directly for those.
      case Some(info) if info.belleExpr == e || info.needsGenerator => info.codeName
      case _ => e match {
        case DefTactic(name, t) => op(e).terminal.img + " " + name + " " + AS.img + " (" + newline(indent+1) + pp(t, indent+1) + newline(indent) + ")"
        case ApplyDefTactic(DefTactic(name, _)) => name
        case e: ExpandAll => e.prettyString
        case e: Expand => e.prettyString
        case SeqTactic(l,r)    => sanitizeBinary(wrapLeft(e, l, indent), op(e).terminal.img, wrapRight(e, r, indent))
        case EitherTactic(l,r) => sanitizeBinary(wrapLeft(e, l, indent), op(e).terminal.img, wrapRight(e, r, indent))
        case BranchTactic(ts) => op(e).terminal.img +
          "(" + newline(indent+1) + ts.map(pp(_, indent+1)).mkString("," + newline(indent+1)) + newline(indent) + ")"
        case CaseTactic(ts) => op(e).terminal.img +
          "(" + newline(indent+1) + ts.map({ case (label, t) => "\"" + label.prettyString + "\": " + pp(t, indent+2) }).mkString("," + newline(indent+1)) + newline(indent) + ")"
        case SaturateTactic(t) => sanitizeUnary(wrapLeft(e, t, indent), op(e).terminal.img)
        case it: StringInputTactic =>
          if (it.inputs.nonEmpty) {
            val eargs = BelleExpr.persistable(it.inputs).flatMap(input => argPrinter(Left(input))).mkString(", ")
            it.name + "(" + eargs + ")"
          } else it.name
        case b@BuiltInTactic(name) => if (!b.isInternal) name else ""
        case b@BuiltInPositionTactic(name) => if (!b.isInternal) name else ""
        case b: CoreLeftTactic => b.name
        case b: CoreRightTactic => b.name
        case b: BuiltInLeftTactic => b.name
        case b: BuiltInRightTactic => b.name
        case e: PartialTactic => wrapLeft(e, e.child, indent) + " " + op(e).terminal.img
        case e: RepeatTactic => wrapLeft(e, e.child, indent) + op(e).terminal.img
        case OnAll(c) => op(e).terminal.img + "(" + pp(c, indent) + ")"
        case Let(abbr, value, inner) => op(e).terminal.img + " (" + argPrinter(Left(
          (abbr, value) match {
            case (a: Term, v: Term) => Equal(a, v)
            case (a: Formula, v: Formula) => edu.cmu.cs.ls.keymaerax.core.Equiv(a, v)
          })).getOrElse("") + ") " + IN.img + " (" +
          newline(indent+1) + pp(inner, indent+1) + newline(indent) + ")"
        case t@DependentPositionTactic(name) =>
          if (!t.isInternal) name // name of a DependentPositionTactic is the codeName
          else throw PrinterException("Anonymous tactic cannot be re-parsed: please replace anonymous tactic with its inner steps.")
        case adp: AppliedDependentPositionTactic => adp.pt match {
          case e: DependentPositionWithAppliedInputTactic =>
            val ins = BelleExpr.persistable(e.inputs)
            val eargs = ins.flatMap(input => argPrinter(Left(input))).mkString(", ")
            val sep = if (eargs.isEmpty) "" else ", "
            e.name + "(" + eargs + sep + argPrinter(Right(adp.locator)).getOrElse("") + ")"
          case e: DependentPositionTactic =>
            val  argStr = argPrinter(Right(adp.locator)).map(s => "(" + s + ")").getOrElse("")
            e.name + argStr //@todo not sure about this.
        }
        case ap : AppliedPositionTactic => pp(ap.positionTactic, indent) + argListPrinter(Right(ap.locator) :: Nil)
        case it : InputTactic =>
          val persist = BelleExpr.persistable(it.inputs)
          val flat = persist.flatMap(input => argPrinter(Left(input)))
          val eargs = flat.mkString(", ")
          val argString = if (eargs.isEmpty) "" else  "(" + eargs + ")"
          it.name + argString
        case t: AppliedBuiltinTwoPositionTactic => t.positionTactic.name + "(" + t.posOne.prettyString + ", " + t.posTwo.prettyString + ")"
        case n@NamedTactic(name, _) =>
          if (!n.isInternal) name
          else throw PrinterException("Anonymous tactic cannot be re-parsed: please replace anonymous tactic with its inner steps.")
        case dot: BelleDot => "_@" + dot.hashCode()
        case LabelBranch(BelleStartTxLabel) => "nil"
        case LabelBranch(BelleLabelTx(BelleSubLabel(BelleRollbackTxLabel, label), None, _)) => LabelBranch(BelleTopLevelLabel(label)).prettyString
        case l: LabelBranch => l.prettyString
        case DependentTactic(name) => name // must be last, otherwise applied dependent tactics lose their position
        case Using(es, t) => (t match {
          case _: SeqTactic | _: EitherTactic | _: RepeatTactic | _: CaseTactic | _: ParallelTactic | _: SaturateTactic
               | _: Using | _: BranchTactic => "(" + pp(t, indent) + ")"
          case _ => pp(t, indent)
        }) + " using \"" + es.mkString(" :: ") + (if (es.isEmpty) "nil" else if (es.size == 1) "" else " :: nil") + "\""
        case _ => throw PrinterException(s"Do not know how to pretty-print $e")
      }
    }
  }

  private def argListPrinter(args: List[BelleParser.TacticArg]) = {
    // Some arguments (Generators) will be automatically instantiated by the interpreter and so should not be persisted explicitly
    if(args.isEmpty)
      ""
    else
      "(" + BelleExpr.persistable(args).flatMap(argPrinter).reduce(_ + ", " + _) + ")"
  }

  // @TODO: Print substitution as subst.subsDefsInput.map(p => p.what.prettyString + "~>" + p.repl.prettyString)
  private def argPrinter(arg: BelleParser.TacticArg): Option[String] = {
    arg match {
      case Left(None) => None
      case Left(Nil) => Some("\"nil\"")
      case Left(x :: Nil) => argPrinter(Left(x))
      case Left(x :: xs) => Some((x :: xs).flatMap(c => argPrinter(Left(c))).map(_.stripPrefix("\"").stripSuffix("\"")).
        mkString("\"", "::", "::nil\""))
      case Left(expr: Expression) => Some("\"" + KeYmaeraXPrettyPrinter(expr) + "\"")
      case Left(pie: PosInExpr) => Some("\"" + pie.pos.mkString(".") + "\"")
      case Left(Some(expr)) => argPrinter(Left(expr))
      case Left(expr) => Some("\"" + expr + "\"")
      case Right(loc) => Some(loc.prettyString)
    }
  }

  private val TAB = "  "
  private def newline(indent: Int) = "\n" + TAB*indent

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
