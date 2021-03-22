/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.core.{Expression, Formula, Term}
import edu.cmu.cs.ls.keymaerax.infrastruct.PosInExpr.HereP
import edu.cmu.cs.ls.keymaerax.infrastruct.{FormulaTools, _}

import scala.util.matching.Regex

////////////////////////////////////////////////////////////////////////////////////////////////////
// Locate Positions
////////////////////////////////////////////////////////////////////////////////////////////////////

/** Position locators identify a position directly or indirectly in a sequent. 
 * @see [[AtPosition.apply()]]
 */
sealed trait PositionLocator {
  def prettyString: String

  def toPosition(p: ProvableSig): Option[Position]
}

object PositionLocator {
  import edu.cmu.cs.ls.keymaerax.core._
  /** #-placeholder expression and regex for matching left/right placeholder; forces parentheses by non-default associativity. */
  def placeholder(e: Expression): (Expression, String, String) = e match {
    case f: Formula =>
      val h = PredOf(Function("h_", None, Unit, Bool, interpreted=false), Nothing)
      (And(And(h, f), h), Regex.quote("(" + h.prettyString + "&"), Regex.quote(")&" + h.prettyString))
    case t: Term =>
      val h = FuncOf(Function("h_", None, Unit, Real, interpreted=false), Nothing)
      (Plus(h, Plus(t, h)), Regex.quote(h.prettyString + "+("), Regex.quote("+" + h.prettyString + ")"))
    case p: Program =>
      val h = ProgramConst("h_")
      (Compose(Compose(h, p), h), Regex.quote("{" + h.prettyString), Regex.quote("}" + h.prettyString))
  }

  def withMarkers(e: Expression, pos: PosInExpr): String = {
    import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
    if (pos == HereP) e.prettyString
    else {
      val (ph, left, right) = placeholder(e.sub(pos).getOrElse(throw new IllegalArgumentException("Sub-position " + pos.prettyString + " does not exist in " + e.prettyString)))
      e.replaceAt(pos, ph).prettyString.
        replaceAll(left, "#").
        replaceAll(right, "#").
        replaceAll("\\(#(.+)#\\)", "#$1#").
        replaceAll("\\{#(.+)#}", "#$1#")
    }
  }

  def withMarkers(s: String, sub: Expression, start: Int, end: Int): (String, Expression) = {
    val (p, _, _) = placeholder(sub)
    (s.patch(start, p.prettyString, end), p)
  }
}

/** Locates the formula at the specified fixed position. Can optionally specify the expected formula or expected shape of formula at that position as contract. */
case class Fixed private[keymaerax] (pos: Position, shape: Option[Expression] = None, exact: Boolean = true) extends PositionLocator {
  override def prettyString: String = (shape, exact) match {
    case (Some(fml), true) => pos.topLevel.prettyString + "==\"" + PositionLocator.withMarkers(fml, pos.inExpr) + "\""
    case (Some(fml), false) => pos.topLevel.prettyString + "~=\"" + PositionLocator.withMarkers(fml, pos.inExpr) + "\""
    case (None, _) => pos.prettyString
  }
  override def toPosition(p: ProvableSig): Option[Position] = Some(pos)
}
object Fixed {
  def apply(seqPos: Int, inExpr: List[Int], shape: Option[Expression], exact: Boolean): Fixed = new Fixed(Position(seqPos, inExpr), shape, exact)
  def apply(seqPos: Int, inExpr: List[Int], shape: Option[Expression]): Fixed = new Fixed(Position(seqPos, inExpr), shape)
  def apply(seqPos: Int, inExpr: List[Int]): Fixed = new Fixed(Position(seqPos, inExpr))
  def apply(seqPos: Int): Fixed = new Fixed(Position(seqPos, Nil))
}

/** Locates the first applicable top-level position that matches shape (exactly or unifiably) at or after position `start` (remaining in antecedent/succedent as `start` says). */
case class Find(goal: Int, shape: Option[Expression], start: Position, exact: Boolean = true) extends PositionLocator {
  private def sub(p: Position): String = if (p.isTopLevel) "" else p.inExpr.prettyString
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

  override def toPosition(p: ProvableSig): Option[Position] = findPosition(p, start)

  /** Finds a position in the provable `p` at or after `pos` that matches the `shape`. */
  def findPosition(p: ProvableSig, pos: Position): Option[Position] = {
    require(start.isIndexDefined(p.subgoals(goal)), "Find must point to a valid position in the sequent, but " + start.prettyString + " is undefined in " + p.subgoals(goal).prettyString)
    shape match {
      case Some(f: Formula) if !exact && UnificationMatch.unifiable(f, p.subgoals(goal)(pos.top)).isDefined => Some(pos)
      case Some(f: Formula) if !exact && UnificationMatch.unifiable(f, p.subgoals(goal)(pos.top)).isEmpty =>
        val nextPos = pos.advanceIndex(1)
        if (nextPos.isIndexDefined(p.subgoals(goal))) findPosition(p, nextPos)
        else None
      case Some(f: Formula) if exact && p.subgoals(goal)(pos.top) == f => Some(pos)
      case Some(f: Formula) if exact && p.subgoals(goal)(pos.top) != f =>
        val nextPos = pos.advanceIndex(1)
        if (nextPos.isIndexDefined(p.subgoals(goal))) findPosition(p, nextPos)
        else None
      case Some(t: Term) =>
        val tPos = FormulaTools.posOf(p.subgoals(goal)(pos.top), e => if (exact) e == t else UnificationMatch.unifiable(e, t).isDefined)
        if (tPos.isEmpty) findPosition(p, pos.advanceIndex(1))
        else Some(pos.topLevel ++ tPos.head)
      case None => Some(pos)
    }
  }
}

object Find {
  /** 'L Find somewhere on the left meaning in the antecedent */
  def FindL(goal: Int, shape: Option[Expression], sub: PosInExpr = HereP, exact: Boolean = true): Find = new Find(goal, shape, AntePosition.base0(0, sub), exact)
  /** 'R Find somewhere on the right meaning in the succedent */
  def FindR(goal: Int, shape: Option[Expression], sub: PosInExpr = HereP, exact: Boolean = true): Find = new Find(goal, shape, SuccPosition.base0(0, sub), exact)
}

/** 'Llast Locates the last position in the antecedent. */
case class LastAnte(goal: Int, inExpr: PosInExpr = PosInExpr.HereP) extends PositionLocator {
  override def prettyString: String = "'Llast" + (if (inExpr != PosInExpr.HereP) inExpr.prettyString else "")
  override def toPosition(p: ProvableSig): Option[Position] = {
    val pos = AntePosition.base0(p.subgoals(goal).ante.length - 1, inExpr)
    if (pos.isIndexDefined(p.subgoals(goal))) Some(pos)
    else None
  }
}

/** 'Rlast Locates the last position in the succedent. */
case class LastSucc(goal: Int, inExpr: PosInExpr = PosInExpr.HereP) extends PositionLocator {
  override def prettyString: String = "'Rlast" + (if (inExpr != PosInExpr.HereP) inExpr.prettyString else "")
  override def toPosition(p: ProvableSig): Option[Position] = {
    val pos = SuccPosition.base0(p.subgoals(goal).succ.length - 1, inExpr)
    if (pos.isIndexDefined(p.subgoals(goal))) Some(pos)
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


