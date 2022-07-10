/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.{Expression, Formula}
import edu.cmu.cs.ls.keymaerax.infrastruct.{AntePosition, PosInExpr, Position, SuccPosition}
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, Location, UnknownLocation}

/** Empty placeholder for compiling. */
sealed class BelleExpr(private var location: Location = UnknownLocation) {

}

case class SeqTactic(seq: Seq[BelleExpr]) extends BelleExpr
object SeqTactic {
  def apply(t1: BelleExpr, t2: BelleExpr): BelleExpr = (t1, t2) match {
    case (SeqTactic(s1), SeqTactic(s2)) => SeqTactic(s1++s2)
    case (SeqTactic(s1), _) => SeqTactic(s1 :+ t2)
    case (_, SeqTactic(s2)) => SeqTactic(t1 +: s2)
    case _ => SeqTactic(Seq(t1, t2))
  }
}

case class EitherTactic(alts: Seq[BelleExpr]) extends BelleExpr
object EitherTactic {
  def apply(t1: BelleExpr, t2: BelleExpr): BelleExpr = (t1, t2) match {
    case (EitherTactic(s1), EitherTactic(s2)) => EitherTactic(s1++s2)
    case (EitherTactic(s1), _) => EitherTactic(s1 :+ t2)
    case (_, EitherTactic(s2)) => EitherTactic(t1 +: s2)
    case _ => EitherTactic(Seq(t1, t2))
  }
}
case class ParallelTactic(expr: List[BelleExpr]) extends BelleExpr
case class SaturateTactic(child: BelleExpr) extends BelleExpr
case class RepeatTactic(child: BelleExpr, times: Int) extends BelleExpr
case class BranchTactic(children: Seq[BelleExpr]) extends BelleExpr
case class CaseTactic(children: Seq[(BelleLabel, BelleExpr)]) extends BelleExpr
case class OnAll(e: BelleExpr) extends BelleExpr

case class Let(abbr: Expression, value: Expression, inner: BelleExpr) extends BelleExpr
case class Using(es: List[Expression], t: BelleExpr) extends BelleExpr
case class PartialTactic(child: BelleExpr, label: Option[BelleLabel] = None) extends BelleExpr
case class DefTactic(name: String, t: BelleExpr) extends BelleExpr
case class ApplyDefTactic(t: DefTactic) extends BelleExpr
