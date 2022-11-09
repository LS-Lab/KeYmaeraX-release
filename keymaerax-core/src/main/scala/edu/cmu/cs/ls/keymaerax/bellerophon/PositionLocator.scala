/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.core.{Expression, Formula, Sequent, Term}
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr.HereP
import edu.cmu.cs.ls.keymaerax.infrastruct.{FormulaTools, _}
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, BuiltinSymbols, Declaration, InterpretedSymbols, KeYmaeraXOmitInterpretationPrettyPrinter, TacticReservedSymbols}

import scala.annotation.tailrec
import scala.util.matching.Regex

////////////////////////////////////////////////////////////////////////////////////////////////////
// Locate Positions
////////////////////////////////////////////////////////////////////////////////////////////////////

/** Position locators identify a position directly or indirectly in a sequent. 
 * @see [[AtPosition.apply()]]
 */
sealed trait PositionLocator {
  /** String representation of this locator. */
  def prettyString: String
  /** Returns the position that this locator points to in the provable `p`. */
  def toPosition(p: ProvableSig): Option[Position]
  /** Returns the position that this locator points to in the sequent `s`. */
  def toPosition(s: Sequent): Option[Position]
}

object PositionLocator {
  import edu.cmu.cs.ls.keymaerax.core._
  private val exprPP = new KeYmaeraXOmitInterpretationPrettyPrinter
  /** #-placeholder expression and regex for matching left/right placeholder; forces parentheses by non-default associativity. */
  def placeholder(e: Expression): (Expression, String, String) = e match {
    case f: Formula =>
      val h = PredOf(Function("h_", None, Unit, Bool), Nothing)
      (And(And(h, f), h), Regex.quote("(" + exprPP(h) + "&"), Regex.quote(")&" + exprPP(h)))
    case t: Term =>
      val h = FuncOf(Function("h_", None, Unit, Real), Nothing)
      (Plus(h, Plus(t, h)), Regex.quote(exprPP(h) + "+("), Regex.quote("+" + exprPP(h) + ")"))
    case p: Program =>
      val h = ProgramConst("h_")
      (Compose(Compose(h, p), h), Regex.quote("{" + exprPP(h)), Regex.quote("}" + exprPP(h)))
  }

  /** Replaces `#` in `s` with parentheses/braces per `kind`. */
  def replaceHashesParenthesized(s: String, kind: Kind): String = {
    val (l, r) = kind match {
      case TermKind | FormulaKind => ("(", ")")
      case ProgramKind => ("{", "}")
    }
    s.replaceFirst("#", l).replaceFirst("#",r)
  }

  def withMarkers(e: Expression, pos: PosInExpr): String = {
    import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
    if (pos == HereP) exprPP(e)
    else {
      val (ph, left, right) = placeholder(e.sub(pos).getOrElse(throw new IllegalArgumentException("Sub-position " + pos.prettyString + " does not exist in " + e.prettyString)))
      exprPP(e.replaceAt(pos, ph)).
        replaceAll(left, "#").
        replaceAll(right, "#").
        replaceAll("\\(#(.+)#\\)", "#$1#").
        replaceAll("\\{#(.+)#}", "#$1#")
    }
  }

  def withMarkers(s: String, sub: Expression, start: Int, end: Int): (String, Expression) = {
    val (p, _, _) = placeholder(sub)
    //@note [[withMarkers]] removes enclosing () and {} for more concise appearance
    val (l, r) = sub.kind match {
      case TermKind | FormulaKind => ("(", ")")
      case ProgramKind => ("{", "}")
    }
    (s.patch(start, l + p.prettyString + r, end), p)
  }
}

/** Locates the formula at the specified fixed position. Can optionally specify the expected formula or expected shape of formula at that position as contract. */
case class Fixed private[keymaerax] (pos: Position, shape: Option[Expression] = None, exact: Boolean = true) extends PositionLocator {
  override def prettyString: String = (shape, exact) match {
    case (Some(fml), true) => pos.topLevel.prettyString + "==\"" + PositionLocator.withMarkers(fml, pos.inExpr) + "\""
    case (Some(fml), false) => pos.topLevel.prettyString + "~=\"" + PositionLocator.withMarkers(fml, pos.inExpr) + "\""
    case (None, _) => pos.prettyString
  }
  /** @inheritdoc */
  override def toPosition(p: ProvableSig): Option[Position] = Some(pos)
  /** @inheritdoc */
  override def toPosition(s: Sequent): Option[Position] = Some(pos)
}
object Fixed {
  def apply(seqPos: Int, inExpr: List[Int], shape: Option[Expression], exact: Boolean): Fixed = new Fixed(Position(seqPos, inExpr), shape, exact)
  def apply(seqPos: Int, inExpr: List[Int], shape: Option[Expression]): Fixed = new Fixed(Position(seqPos, inExpr), shape)
  def apply(seqPos: Int, inExpr: List[Int]): Fixed = new Fixed(Position(seqPos, inExpr))
  def apply(seqPos: Int): Fixed = new Fixed(Position(seqPos, Nil))
}

/** Locates the first applicable top-level position that matches shape (exactly or unifiably) at or after position `start` (remaining in antecedent/succedent as `start` says). */
case class Find(goal: Int, shape: Option[Expression], start: Position, exact: Boolean,
                defs: Declaration) extends PositionLocator {
  private lazy val substShape = shape.map(defs.exhaustiveSubst[Expression])

  /** Prints the string representation of the sub-position (`inExpr`) of position `p`. */
  private def sub(p: Position): String = if (p.isTopLevel) "" else p.inExpr.prettyString
  /** @inheritdoc */
  override def prettyString: String = (start, shape, exact) match {
    case (l: AntePosition, None, _) => "'L" + sub(l)
    case (l: AntePosition, Some(s), true) => "'L==\"" + PositionLocator.withMarkers(s, l.inExpr) + "\""
    case (l: AntePosition, Some(s), false) => "'L~=\"" + PositionLocator.withMarkers(s, l.inExpr)  + "\""
    case (r: SuccPosition, None, _) => "'R" + sub(r)
    case (r: SuccPosition, Some(s), true) => "'R==\"" + PositionLocator.withMarkers(s, r.inExpr) + "\""
    case (r: SuccPosition, Some(s), false) => "'R~=\"" + PositionLocator.withMarkers(s, r.inExpr)  + "\""
    case (p, None, _) => "'_" + sub(p)
    case (p, Some(s), true) => "'_==\"" + PositionLocator.withMarkers(s, p.inExpr)  + "\""
    case (p, Some(s), false) => "'_~=\"" + PositionLocator.withMarkers(s, p.inExpr)  + "\""
  }

  /** @inheritdoc */
  override def toPosition(p: ProvableSig): Option[Position] = findPosition(p, start)
  /** @inheritdoc */
  override def toPosition(s: Sequent): Option[Position] = findPosition(s, start)

  /** Finds a position in the provable `p` at or after `pos` that matches the shape of this locator. */
  def findPosition(p: ProvableSig, pos: Position): Option[Position] = findPosition(p.subgoals(goal), pos)

  /** Finds a position in the sequent `s` at or after `pos` that matches the `shape` of this locator. */
  @tailrec
  final def findPosition(s: Sequent, pos: Position): Option[Position] = {
    require(start.isIndexDefined(s), "Find must point to a valid position in the sequent, but " + start.prettyString + " is undefined in " + s.prettyString)
    shape match {
      case Some(f: Formula) =>
        if (!exact) {
          if (UnificationMatch.unifiable(f, s(pos.top)).isDefined) {
            Some(pos)
          } else {
            val nextPos = pos.advanceIndex(1)
            if (nextPos.isIndexDefined(s)) findPosition(s, nextPos)
            else None
          }
        } else if (s(pos.top) == f || defs.exhaustiveSubst(s(pos.top)) == substShape.get) {
          Some(pos)
        } else  {
          val nextPos = pos.advanceIndex(1)
          if (nextPos.isIndexDefined(s)) findPosition(s, nextPos)
          else None
        }
      case Some(t: Term) =>
        val tPos = FormulaTools.posOf(s(pos.top), e => if (exact) e == t else UnificationMatch.unifiable(e, t).isDefined)
        if (tPos.isEmpty) findPosition(s, pos.advanceIndex(1))
        else Some(pos.topLevel ++ tPos.head)
      case None => Some(pos)
    }
  }
}

object Find {
  /** 'L Find somewhere on the left meaning in the antecedent */
  def FindL(goal: Int, shape: Option[Expression], sub: PosInExpr, exact: Boolean, defs: Declaration): Find =
    new Find(goal, shape, AntePosition.base0(0, sub), exact, defs)
  def FindLDef(shape: Expression, sub: PosInExpr, defs: Declaration): Find =
    new Find(0, Some(shape), AntePosition.base0(0, sub), exact=true, defs)
  def FindLPlain(shape: Expression, sub: PosInExpr): Find = FindLDef(shape, sub, BuiltinSymbols.all)
  def FindLPlain(shape: Expression): Find = FindLPlain(shape, HereP)
  val FindLFirst: Find = new Find(0, None, AntePosition.base0(0), exact=true, BuiltinSymbols.all)
  def FindLMatch(shape: Expression): Find =
    new Find(0, Some(shape), AntePosition.base0(0), exact=false, BuiltinSymbols.all)
  def FindLAfter(shape: Option[Expression], start: AntePosition): Find =
    new Find(0, shape, start, exact=true, BuiltinSymbols.all)
  /** 'R Find somewhere on the right meaning in the succedent */
  def FindR(goal: Int, shape: Option[Expression], sub: PosInExpr, exact: Boolean, defs: Declaration): Find =
    new Find(goal, shape, SuccPosition.base0(0, sub), exact, defs)
  def FindRDef(shape: Expression, sub: PosInExpr, defs: Declaration): Find =
    new Find(0, Some(shape), SuccPosition.base0(0, sub), exact=true, defs)
  def FindRPlain(shape: Expression, sub: PosInExpr): Find = FindRDef(shape, sub, BuiltinSymbols.all)
  def FindRPlain(shape: Expression): Find = FindRPlain(shape, HereP)
  val FindRFirst: Find = new Find(0, None, SuccPosition.base0(0), exact=true, BuiltinSymbols.all)
  def FindRMatch(shape: Expression): Find =
    new Find(0, Some(shape), SuccPosition.base0(0), exact=false, BuiltinSymbols.all)
  def FindRAfter(shape: Option[Expression], start: SuccPosition): Find =
    new Find(0, shape, start, exact=true, BuiltinSymbols.all)
}

/** 'Llast Locates the last position in the antecedent. */
case class LastAnte(goal: Int, inExpr: PosInExpr = PosInExpr.HereP) extends PositionLocator {
  /** @inheritdoc */
  override def prettyString: String = "'Llast" + (if (inExpr != PosInExpr.HereP) inExpr.prettyString else "")
  /** @inheritdoc */
  override def toPosition(p: ProvableSig): Option[Position] = toPosition(p.subgoals(goal))
  /** @inheritdoc */
  override def toPosition(s: Sequent): Option[Position] = {
    val pos = AntePosition.base0(s.ante.length - 1, inExpr)
    if (pos.isIndexDefined(s)) Some(pos)
    else None
  }
}

/** 'Rlast Locates the last position in the succedent. */
case class LastSucc(goal: Int, inExpr: PosInExpr = PosInExpr.HereP) extends PositionLocator {
  /** @inheritdoc */
  override def prettyString: String = "'Rlast" + (if (inExpr != PosInExpr.HereP) inExpr.prettyString else "")
  /** @inheritdoc */
  override def toPosition(p: ProvableSig): Option[Position] = toPosition(p.subgoals(goal))
  /** @inheritdoc */
  override def toPosition(s: Sequent): Option[Position] = {
    val pos = SuccPosition.base0(s.succ.length - 1, inExpr)
    if (pos.isIndexDefined(s)) Some(pos)
    else None
  }
}

///**
//  * Abstract positions are either actual positions, or else indicate that the tactic should point back to a position
//  * that was generated by a previous tactic.
//  *
//  * Example:
//  * {{{
//  *   AndR(SuccPos(2)) <(
//  *     ImplyR(GeneratedPosition()) & TrivialCloser,
//  *     ImplyR(GeneratedPosition()) & TrivialCloser
//  *   )
//  * }}}
//  *
//  * is equivalent to:
//  *
//  * {{{
//  *   AndR(SuccPos(2)) <(
//  *     ImplyR(SuccPos(2)) & ...,
//  *     ImplyR(SuccPos(2)) & ...
//  *   )
//  * }}}
//  *
//  * @todo Not currently using these; one thing at at a time.
//  */
//sealed trait AbstractPosition
//case class AbsolutePosition(p : Position) extends AbstractPosition
//case class GeneratedPosition()              extends AbstractPosition
//


