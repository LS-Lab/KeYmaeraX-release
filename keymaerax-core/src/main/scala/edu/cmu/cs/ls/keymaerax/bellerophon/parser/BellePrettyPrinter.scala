package edu.cmu.cs.ls.keymaerax.bellerophon.parser

import edu.cmu.cs.ls.keymaerax.bellerophon._
import BelleOpSpec.op
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser.{DOUBLE_COLON, DOUBLE_QUOTE, EMPTY_ARGS, EMPTY_BRANCHES, EMPTY_TACTIC, LIST_END, NEWLINE, SPACE, TAB, TODO_TACTIC}
import edu.cmu.cs.ls.keymaerax.btactics.macros.TacticInfo
import edu.cmu.cs.ls.keymaerax.core.{Equal, Expression, Formula, Term}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXOmitInterpretationPrettyPrinter
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

  /** Pretty-printer for expressions. */
  private val exprPP = new KeYmaeraXOmitInterpretationPrettyPrinter

  private def sanitizeUnary(t: String, op: String): String = t match {
    case EMPTY_TACTIC | EMPTY_BRANCHES => EMPTY_TACTIC
    case _ => t + op
  }

  private def sanitizeBinary(left: String, op: String, right: String, sep: String = SPACE): String = left match {
    case EMPTY_TACTIC | EMPTY_BRANCHES => right match {
      case EMPTY_TACTIC | EMPTY_BRANCHES => EMPTY_TACTIC
      case _ => right
    }
    case _ => right match {
      case EMPTY_TACTIC | EMPTY_BRANCHES => left
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
        case DefTactic(name, t) => op(e).terminal.img + SPACE + name + SPACE + AS.img + SPACE + OPEN_PAREN.img + newline(indent+1) + pp(t, indent+1) + newline(indent) + CLOSE_PAREN.img
        case ApplyDefTactic(DefTactic(name, _)) => name
        case SeqTactic(l +: (r: SeqTactic) +: Nil) => sanitizeBinary(wrapLeft(e, l, indent), op(e).terminal.img, wrap(r, indent))
        case SeqTactic(l +: r +: Nil) => sanitizeBinary(wrapLeft(e, l, indent), op(e).terminal.img, wrapRight(e, r, indent))
        case SeqTactic(s +: t) => sanitizeBinary(wrapLeft(e, s, indent), op(e).terminal.img, wrapRight(e, SeqTactic(t), indent))
        case EitherTactic(l +: (r: EitherTactic) +: Nil) => sanitizeBinary(wrapLeft(e, l, indent), op(e).terminal.img, wrap(r, indent))
        case EitherTactic(l +: r +: Nil) => sanitizeBinary(wrapLeft(e, l, indent), op(e).terminal.img, wrapRight(e, r, indent))
        case EitherTactic(s +: t) => sanitizeBinary(wrapLeft(e, s, indent), op(e).terminal.img, wrapRight(e, EitherTactic(t), indent))
        case BranchTactic(ts) => op(e).terminal.img +
          OPEN_PAREN.img + newline(indent+1) + ts.map(pp(_, indent+1)).mkString(COMMA.img + newline(indent+1)) + newline(indent) + CLOSE_PAREN.img
        case CaseTactic(ts) => op(e).terminal.img +
          OPEN_PAREN.img + newline(indent+1) + ts.map({ case (label, t) => DOUBLE_QUOTE + label.prettyString + DOUBLE_QUOTE + COLON.img + SPACE + pp(t, indent+2) }).mkString(COMMA.img + newline(indent+1)) + newline(indent) + CLOSE_PAREN.img
        case SaturateTactic(t) => sanitizeUnary(wrapLeft(e, t, indent), op(e).terminal.img)
        case it: StringInputTactic =>
          if (it.inputs.nonEmpty) {
            val eargs = BelleExpr.persistable(it.inputs).flatMap(input => argPrinter(Left(input))).mkString(COMMA.img + SPACE)
            it.name + OPEN_PAREN.img + eargs + CLOSE_PAREN.img
          } else it.name
        case b@BuiltInTactic(name) => if (!b.isInternal) name else EMPTY_TACTIC
        case b@BuiltInPositionTactic(name) => if (!b.isInternal) name else EMPTY_TACTIC
        case b: CoreLeftTactic => b.name
        case b: CoreRightTactic => b.name
        case b: BuiltInLeftTactic => b.name
        case b: BuiltInRightTactic => b.name
        case e: PartialTactic => wrapLeft(e, e.child, indent) + SPACE + op(e).terminal.img
        case e: RepeatTactic => wrapLeft(e, e.child, indent) + op(e).terminal.img
        case OnAll(c) => op(e).terminal.img + OPEN_PAREN.img + pp(c, indent) + CLOSE_PAREN.img
        case Let(abbr, value, inner) => op(e).terminal.img + SPACE + OPEN_PAREN.img + argPrinter(Left(
          (abbr, value) match {
            case (a: Term, v: Term) => Equal(a, v)
            case (a: Formula, v: Formula) => edu.cmu.cs.ls.keymaerax.core.Equiv(a, v)
          })).getOrElse(EMPTY_ARGS) + CLOSE_PAREN.img + SPACE + IN.img + SPACE + OPEN_PAREN.img +
          newline(indent+1) + pp(inner, indent+1) + newline(indent) + CLOSE_PAREN.img
        case t@DependentPositionTactic(name) =>
          if (!t.isInternal) name // name of a DependentPositionTactic is the codeName
          else throw PrinterException("Anonymous tactic cannot be re-parsed: please replace anonymous tactic with its inner steps.")
        case adp: AppliedDependentPositionTactic => adp.pt match {
          case e: DependentPositionWithAppliedInputTactic =>
            val ins = BelleExpr.persistable(e.inputs)
            val eargs = ins.flatMap(input => argPrinter(Left(input))).mkString(COMMA.img + SPACE)
            val sep = if (eargs.isEmpty) EMPTY_ARGS else COMMA.img + SPACE
            e.name + OPEN_PAREN.img + eargs + sep + argPrinter(Right(adp.locator)).getOrElse(EMPTY_ARGS) + CLOSE_PAREN.img
          case e: DependentPositionTactic =>
            val  argStr = argPrinter(Right(adp.locator)).map(s => OPEN_PAREN.img + s + CLOSE_PAREN.img).getOrElse(EMPTY_ARGS)
            e.name + argStr //@todo not sure about this.
        }
        case ap : AppliedPositionTactic => pp(ap.positionTactic, indent) + argListPrinter(Right(ap.locator) :: Nil)
        case it : InputTactic =>
          val persist = BelleExpr.persistable(it.inputs)
          val flat = persist.flatMap(input => argPrinter(Left(input)))
          val eargs = flat.mkString(COMMA.img + SPACE)
          val argString = if (eargs.isEmpty) EMPTY_ARGS else  OPEN_PAREN.img + (if (eargs=="\"nil\"") EMPTY_ARGS else eargs) + CLOSE_PAREN.img
          it.name + argString
        case t: AppliedBuiltinTwoPositionTactic => t.positionTactic.name + OPEN_PAREN.img + t.posOne.prettyString + COMMA.img + SPACE + t.posTwo.prettyString + CLOSE_PAREN.img
        case n@NamedTactic(name, _) =>
          if (!n.isInternal) name
          else throw PrinterException("Anonymous tactic cannot be re-parsed: please replace anonymous tactic with its inner steps.")
        case dot: BelleDot => "_@" + dot.hashCode()
        case LabelBranch(BelleStartTxLabel) => TODO_TACTIC
        case LabelBranch(BelleLabelTx(BelleSubLabel(BelleRollbackTxLabel, label), None, _)) => LabelBranch(BelleTopLevelLabel(label)).prettyString
        case l: LabelBranch => l.prettyString
        case DependentTactic(name) => name // must be last, otherwise applied dependent tactics lose their position
        case Using(es, t) => (t match {
          case _: SeqTactic | _: EitherTactic | _: RepeatTactic | _: CaseTactic | _: ParallelTactic | _: SaturateTactic
               | _: Using | _: BranchTactic => OPEN_PAREN.img + pp(t, indent) + CLOSE_PAREN.img
          case _ => pp(t, indent)
        }) + SPACE + USING.img + SPACE + DOUBLE_QUOTE + es.map(KeYmaeraXOmitInterpretationPrettyPrinter).mkString(SPACE + DOUBLE_COLON + SPACE) + (if (es.isEmpty) LIST_END else if (es.size == 1) "" else SPACE + DOUBLE_COLON + SPACE + LIST_END) + DOUBLE_QUOTE
        case _ => throw PrinterException(s"Do not know how to pretty-print $e")
      }
    }
  }

  private def argListPrinter(args: List[BelleParser.TacticArg]) = {
    // Some arguments (Generators) will be automatically instantiated by the interpreter and so should not be persisted explicitly
    if(args.isEmpty)
      EMPTY_ARGS
    else
      OPEN_PAREN.img + BelleExpr.persistable(args).flatMap(argPrinter).reduce(_ + COMMA + SPACE + _) + CLOSE_PAREN.img
  }

  // @TODO: Print substitution as subst.subsDefsInput.map(p => p.what.prettyString + "~>" + p.repl.prettyString)
  private def argPrinter(arg: BelleParser.TacticArg): Option[String] = {
    arg match {
      case Left(None) => None
      case Left(Nil) => Some(DOUBLE_QUOTE + LIST_END + DOUBLE_QUOTE)
      case Left(x :: Nil) => argPrinter(Left(x))
      case Left(x :: xs) => Some((x :: xs).flatMap(c => argPrinter(Left(c))).map(_.stripPrefix(DOUBLE_QUOTE).stripSuffix(DOUBLE_QUOTE)).
        mkString(DOUBLE_QUOTE, DOUBLE_COLON, DOUBLE_COLON + LIST_END + DOUBLE_QUOTE))
      case Left(expr: Expression) => Some(DOUBLE_QUOTE + exprPP(expr) + DOUBLE_QUOTE)
      case Left(pie: PosInExpr) => Some(DOUBLE_QUOTE + pie.prettyString + DOUBLE_QUOTE)
      case Left(Some(expr)) => argPrinter(Left(expr))
      case Left(expr) => Some(DOUBLE_QUOTE + expr + DOUBLE_QUOTE)
      case Right(loc) => Some(loc.prettyString)
    }
  }

  private def newline(indent: Int) = NEWLINE + TAB*indent

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

  private def wrap(e : BelleExpr, indent: Int) = OPEN_PAREN.img + pp(e, indent) + CLOSE_PAREN.img
}


case class PrinterException(msg: String) extends Exception(msg)
