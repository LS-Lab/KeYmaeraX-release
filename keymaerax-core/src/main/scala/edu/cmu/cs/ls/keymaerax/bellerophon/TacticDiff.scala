/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.Idioms
import TacticComparator._

sealed trait BelleContext extends (Map[BelleDot, BelleExpr] => BelleExpr) {
  /** Return the result of instantiating this context with argument `t`.
    * That is filling the respective placeholder `p` of this context with tactic `t`. */
  def apply(repl: Map[BelleDot, BelleExpr]): BelleExpr
}

case class ReplacementBelleContext(t: BelleExpr) extends BelleContext {
  override def apply(repl: Map[BelleDot, BelleExpr]): BelleExpr = replace(t, repl)

  def replace(in: BelleExpr, repl: Map[BelleDot, BelleExpr]): BelleExpr = in match {
    case SeqTactic(l, r)    => SeqTactic(replace(l, repl), replace(r, repl))
    case EitherTactic(l, r) => EitherTactic(replace(l, repl), replace(r, repl))
    case SaturateTactic(c)  => SaturateTactic(replace(c, repl))
    case RepeatTactic(c, n) => RepeatTactic(replace(c, repl), n)
    case BranchTactic(c)    => BranchTactic(c.map(replace(_, repl)))
    case OnAll(c)           => OnAll(replace(c, repl))
    // atomic
    case b: BelleDot => repl.getOrElse(b, b)
    case _ => in
  }
}

object TacticComparator {
  import scala.language.implicitConversions
  implicit def TToTacticComparator[T <: BelleExpr](e: T): TacticComparator[T] = new TacticComparator[T](e)
}

class TacticComparator[T <: BelleExpr](val l: T) {
  def ===(r: T): Boolean = (l, r) match {
    case (SeqTactic(ll, lr), SeqTactic(rl, rr)) => ll===rl && lr===rr
    case (SeqTactic(ll, lr), _) if lr==Idioms.nil => ll===r
    case (SeqTactic(ll, lr), _) if ll==Idioms.nil => lr===r
    case _ => l == r
  }
}

/**
  * Computes a diff. (C,d1,d2) of two tactics t1 and t2 such that C(d1)=t1 and C(d2)=t2.
  * @author Stefan Mitsch
  */
object TacticDiff {

  type Diff = (ReplacementBelleContext, Map[BelleDot, BelleExpr], Map[BelleDot, BelleExpr])

  def diff(t1: BelleExpr, t2: BelleExpr): Diff = (t1 match {
    case SeqTactic(l1, r1) => t2 match {
      case SeqTactic(l2, r2) =>
        val d1 = diff(l1, l2)
        val d2 = diff(r1, r2)
        (ReplacementBelleContext(SeqTactic(d1._1.t, d2._1.t)), d1._2++d2._2, d1._3++d2._3)
      case _ =>
        val p = new BelleDot()
        (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
    }
    case EitherTactic(l1, r1) => t2 match {
      case EitherTactic(l2, r2) =>
        val d1 = diff(l1, l2)
        val d2 = diff(r1, r2)
        (ReplacementBelleContext(EitherTactic(d1._1.t, d2._1.t)), d1._2++d2._2, d1._3++d2._3)
      case _ =>
        val p = new BelleDot()
        (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
    }
    case SaturateTactic(c1) => t2 match {
      case SaturateTactic(c2) =>
        val d = diff(c1, c2)
        (ReplacementBelleContext(SaturateTactic(d._1.t)), d._2, d._3)
      case _ =>
        val p = new BelleDot()
        (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
    }
    case RepeatTactic(c1, n1) => t2 match {
      case RepeatTactic(c2, n2) if n1 == n2 =>
        val d = diff(c1, c2)
        (ReplacementBelleContext(RepeatTactic(d._1.t, n1)), d._2, d._3)
      case _ =>
        val p = new BelleDot()
        (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
    }
    case BranchTactic(c1) => t2 match {
      case BranchTactic(c2) if c1.length == c2.length =>
        val ds: Seq[Diff] = c1.zip(c2).map(ts => diff(ts._1, ts._2))
        (ReplacementBelleContext(BranchTactic(ds.map(_._1.t))), ds.map(_._2).reduce(_++_), ds.map(_._3).reduce(_++_))
      case _ =>
        val p = new BelleDot()
        (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
    }
    case OnAll(c1) => t2 match {
      case OnAll(c2) =>
        val d = diff(c1, c2)
        (ReplacementBelleContext(OnAll(d._1.t)), d._2, d._3)
      case _ =>
        val p = new BelleDot()
        (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
    }
    // atomic cases
    case BuiltInTactic(n1) => t2 match {
      case BuiltInTactic(n2) if n1 == n2 => (ReplacementBelleContext(t1), Map[BelleDot, BelleExpr](), Map[BelleDot, BelleExpr]())
      case SeqTactic(n2l, n2r) if t1 == n2l =>
        val p = new BelleDot()
        (ReplacementBelleContext(SeqTactic(t1, p)), Map(p -> Idioms.nil), Map(p -> n2r))
      case _ =>
        val p = new BelleDot()
        (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
    }
    case NamedTactic(n1, c1) => t2 match {
      case NamedTactic(n2, c2) if n1 == n2 && c1 == c2 => (ReplacementBelleContext(t1), Map[BelleDot, BelleExpr](), Map[BelleDot, BelleExpr]())
      case SeqTactic(n2l, n2r) if t1 == n2l =>
        val p = new BelleDot()
        (ReplacementBelleContext(SeqTactic(t1, p)), Map(p -> Idioms.nil), Map(p -> n2r))
      case _ =>
        val p = new BelleDot()
        (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
    }
    case DependentTactic(n1) => t2 match {
      case DependentTactic(n2) if n1 == n2 => (ReplacementBelleContext(t1), Map[BelleDot, BelleExpr](), Map[BelleDot, BelleExpr]())
      case SeqTactic(n2l, n2r) if t1 == n2l =>
        val p = new BelleDot()
        (ReplacementBelleContext(SeqTactic(t1, p)), Map(p -> Idioms.nil), Map(p -> n2r))
      case _ =>
        val p = new BelleDot()
        (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
    }
    case AppliedPositionTactic(c1, l1) => t2 match {
      case AppliedPositionTactic(c2, l2) if c1 == c2 && l1 == l2 => (ReplacementBelleContext(t1), Map[BelleDot, BelleExpr](), Map[BelleDot, BelleExpr]())
      case SeqTactic(n2l, n2r) if t1 == n2l =>
        val p = new BelleDot()
        (ReplacementBelleContext(SeqTactic(t1, p)), Map(p -> Idioms.nil), Map(p -> n2r))
      case _ =>
        val p = new BelleDot()
        (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
    }
    case AppliedBuiltinTwoPositionTactic(c1, p1L, p1R) => t2 match {
      case AppliedBuiltinTwoPositionTactic(c2, p2L, p2R) if c1 == c2 && p1L == p2L && p1R == p2R => (ReplacementBelleContext(t1), Map[BelleDot, BelleExpr](), Map[BelleDot, BelleExpr]())
      case SeqTactic(n2l, n2r) if t1 == n2l =>
        val p = new BelleDot()
        (ReplacementBelleContext(SeqTactic(t1, p)), Map(p -> Idioms.nil), Map(p -> n2r))
      case _ =>
        val p = new BelleDot()
        (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
    }
    case it1: AppliedDependentPositionTacticWithAppliedInput => t2 match {
      case it2: AppliedDependentPositionTacticWithAppliedInput if it1.pt == it2.pt => (ReplacementBelleContext(t1), Map[BelleDot, BelleExpr](), Map[BelleDot, BelleExpr]())
      case SeqTactic(n2l, n2r) if t1 == n2l =>
        val p = new BelleDot()
        (ReplacementBelleContext(SeqTactic(t1, p)), Map(p -> Idioms.nil), Map(p -> n2r))
      case _ =>
        val p = new BelleDot()
        (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
    }
    case InputTactic(n1, i1) => t2 match {
      case InputTactic(n2, i2) if n1 == n2 && i1 == i2 => (ReplacementBelleContext(t1), Map[BelleDot, BelleExpr](), Map[BelleDot, BelleExpr]())
        case SeqTactic(n2l, n2r) if t1 == n2l =>
        val p = new BelleDot()
        (ReplacementBelleContext(SeqTactic(t1, p)), Map(p -> Idioms.nil), Map(p -> n2r))
      case _ =>
        val p = new BelleDot()
        (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
    }
  }) ensuring(r => r._1(r._2)===t1 && r._1(r._3)===t2, "Reapplying context expected to produce original tactics")
}
