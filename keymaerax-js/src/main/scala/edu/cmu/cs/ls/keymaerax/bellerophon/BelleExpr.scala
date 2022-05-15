/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.{Expression,Formula}
import edu.cmu.cs.ls.keymaerax.infrastruct.{Position,AntePosition,SuccPosition,PosInExpr}
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, Location, UnknownLocation}

/** Empty placeholder for compiling. */
sealed class BelleExpr(private var location: Location = UnknownLocation) {

}

sealed trait PositionLocator {}
case class Fixed private[keymaerax] (pos: Position, shape: Option[Formula] = None, exact: Boolean = true) extends PositionLocator
case class Find(goal: Int, shape: Option[Expression], start: Position, exact: Boolean = true, defs: Declaration) extends PositionLocator
object Find {
  def FindL(goal: Int, shape: Option[Expression], sub: PosInExpr, exact: Boolean, defs: Declaration): Find =
    new Find(goal, shape, AntePosition.base0(0, sub), exact, defs)
  def FindR(goal: Int, shape: Option[Expression], sub: PosInExpr, exact: Boolean, defs: Declaration): Find =
    new Find(goal, shape, SuccPosition.base0(0, sub), exact, defs)
}
case class LastAnte(goal: Int, inExpr: PosInExpr = PosInExpr.HereP) extends PositionLocator
case class LastSucc(goal: Int, inExpr: PosInExpr = PosInExpr.HereP) extends PositionLocator

case class SeqTactic(seq: Seq[BelleExpr]) extends BelleExpr
case class EitherTactic(alts: Seq[BelleExpr]) extends BelleExpr
case class ParallelTactic(expr: List[BelleExpr]) extends BelleExpr
case class SaturateTactic(child: BelleExpr) extends BelleExpr
case class RepeatTactic(child: BelleExpr, times: Int) extends BelleExpr
case class BranchTactic(children: Seq[BelleExpr]) extends BelleExpr
case class OnAll(e: BelleExpr) extends BelleExpr