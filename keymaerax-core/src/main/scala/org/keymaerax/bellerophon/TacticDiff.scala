/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.bellerophon

import org.keymaerax.btactics.TactixLibrary
import TacticComparator._
import org.keymaerax.core.Ensures

sealed trait BelleContext extends (Map[BelleDot, BelleExpr] => BelleExpr) {

  /**
   * Return the result of instantiating this context with argument `t`. That is filling the respective placeholder `p`
   * of this context with tactic `t`.
   */
  def apply(repl: Map[BelleDot, BelleExpr]): BelleExpr
}

case class ReplacementBelleContext(t: BelleExpr) extends BelleContext {
  override def apply(repl: Map[BelleDot, BelleExpr]): BelleExpr = replace(t, repl)

  def replace(in: BelleExpr, repl: Map[BelleDot, BelleExpr]): BelleExpr = in match {
    case SeqTactic(s) => SeqTactic(s.map(replace(_, repl)))
    case EitherTactic(s) => EitherTactic(s.map(replace(_, repl)))
    case SaturateTactic(c) => SaturateTactic(replace(c, repl))
    case RepeatTactic(c, n) => RepeatTactic(replace(c, repl), n)
    case BranchTactic(c) => BranchTactic(c.map(replace(_, repl)))
    case OnAll(c) => OnAll(replace(c, repl))
    case DefTactic(n, c) => DefTactic(n, replace(c, repl))
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
    case (SeqTactic(sl), SeqTactic(sr)) =>
      sl.filter(_ != TactixLibrary.nil).zip(sr.filter(_ != TactixLibrary.nil)).forall({ case (ll, lr) => ll === lr })
    case (SeqTactic(s), _) if s.contains(TactixLibrary.nil) => SeqTactic(s.filter(_ != TactixLibrary.nil)) === r
    case (BranchTactic(bl), BranchTactic(br)) => bl.size == br.size && bl.zip(br).forall(x => x._1 === x._2)
    case (EitherTactic(sl), EitherTactic(sr)) =>
      sl.filter(_ != TactixLibrary.nil).zip(sr.filter(_ != TactixLibrary.nil)).forall({ case (ll, lr) => ll === lr })
    case (EitherTactic(s), _) if s.contains(TactixLibrary.nil) => EitherTactic(s.filter(_ != TactixLibrary.nil)) === r
    case (SaturateTactic(sl), SaturateTactic(sr)) => sl === sr
    case (RepeatTactic(rl, nl), RepeatTactic(rr, nr)) => nl == nr && rl === rr
    case (OnAll(al), OnAll(ar)) => al === ar
    case (DefTactic(nl, al), DefTactic(nr, ar)) => nl == nr && al === ar
    case _ => l == r
  }
}

/**
 * Computes a diff. (C,d1,d2) of two tactics t1 and t2 such that C(d1)=t1 and C(d2)=t2.
 * @author
 *   Stefan Mitsch
 */
object TacticDiff {

  type Diff = (ReplacementBelleContext, Map[BelleDot, BelleExpr], Map[BelleDot, BelleExpr])

  def diff(t1: BelleExpr, t2: BelleExpr): Diff =
    (t1 match {
      case SeqTactic(l :: lrem) => t2 match {
          case SeqTactic(r :: rrem) =>
            val d1 = diff(l, r)
            val d2 = diff(SeqTactic(lrem), SeqTactic(rrem))
            (ReplacementBelleContext(SeqTactic(d1._1.t, d2._1.t)), d1._2 ++ d2._2, d1._3 ++ d2._3)
          case _ =>
            val p = new BelleDot()
            (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
        }
      case EitherTactic(l :: lrem) => t2 match {
          case EitherTactic(r :: rrem) =>
            val d1 = diff(l, r)
            val d2 = diff(EitherTactic(lrem), EitherTactic(rrem))
            (ReplacementBelleContext(EitherTactic(d1._1.t, d2._1.t)), d1._2 ++ d2._2, d1._3 ++ d2._3)
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
            (
              ReplacementBelleContext(BranchTactic(ds.map(_._1.t))),
              ds.map(_._2).reduce(_ ++ _),
              ds.map(_._3).reduce(_ ++ _),
            )
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
          case BuiltInTactic(n2) if n1 == n2 =>
            (ReplacementBelleContext(t1), Map[BelleDot, BelleExpr](), Map[BelleDot, BelleExpr]())
          case SeqTactic(n2l :: n2r) if t1 == n2l =>
            val p = new BelleDot()
            (ReplacementBelleContext(SeqTactic(t1, p)), Map(p -> TactixLibrary.nil), Map(p -> SeqTactic(n2r)))
          case _ =>
            val p = new BelleDot()
            (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
        }
      case NamedTactic(n1, c1) => t2 match {
          case NamedTactic(n2, c2) if n1 == n2 && c1 == c2 =>
            (ReplacementBelleContext(t1), Map[BelleDot, BelleExpr](), Map[BelleDot, BelleExpr]())
          case SeqTactic(n2l :: n2r) if t1 == n2l =>
            val p = new BelleDot()
            (ReplacementBelleContext(SeqTactic(t1, p)), Map(p -> TactixLibrary.nil), Map(p -> SeqTactic(n2r)))
          case _ =>
            val p = new BelleDot()
            (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
        }
      case DependentTactic(n1) => t2 match {
          case DependentTactic(n2) if n1 == n2 =>
            (ReplacementBelleContext(t1), Map[BelleDot, BelleExpr](), Map[BelleDot, BelleExpr]())
          case SeqTactic(n2l :: n2r) if t1 == n2l =>
            val p = new BelleDot()
            (ReplacementBelleContext(SeqTactic(t1, p)), Map(p -> TactixLibrary.nil), Map(p -> SeqTactic(n2r)))
          case _ =>
            val p = new BelleDot()
            (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
        }
      case AppliedPositionTactic(c1, l1) => t2 match {
          case AppliedPositionTactic(c2, l2) if c1 == c2 && l1 == l2 =>
            (ReplacementBelleContext(t1), Map[BelleDot, BelleExpr](), Map[BelleDot, BelleExpr]())
          case SeqTactic(n2l :: n2r) if t1 == n2l =>
            val p = new BelleDot()
            (ReplacementBelleContext(SeqTactic(t1, p)), Map(p -> TactixLibrary.nil), Map(p -> SeqTactic(n2r)))
          case _ =>
            val p = new BelleDot()
            (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
        }
      case AppliedBuiltinTwoPositionTactic(c1, p1L, p1R) => t2 match {
          case AppliedBuiltinTwoPositionTactic(c2, p2L, p2R) if c1 == c2 && p1L == p2L && p1R == p2R =>
            (ReplacementBelleContext(t1), Map[BelleDot, BelleExpr](), Map[BelleDot, BelleExpr]())
          case SeqTactic(n2l :: n2r) if t1 == n2l =>
            val p = new BelleDot()
            (ReplacementBelleContext(SeqTactic(t1, p)), Map(p -> TactixLibrary.nil), Map(p -> SeqTactic(n2r)))
          case _ =>
            val p = new BelleDot()
            (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
        }
      case it1: AppliedDependentPositionTacticWithAppliedInput => t2 match {
          case it2: AppliedDependentPositionTacticWithAppliedInput if it1.pt == it2.pt =>
            (ReplacementBelleContext(t1), Map[BelleDot, BelleExpr](), Map[BelleDot, BelleExpr]())
          case SeqTactic(n2l :: n2r) if t1 == n2l =>
            val p = new BelleDot()
            (ReplacementBelleContext(SeqTactic(t1, p)), Map(p -> TactixLibrary.nil), Map(p -> SeqTactic(n2r)))
          case _ =>
            val p = new BelleDot()
            (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
        }
      case InputTactic(n1, i1) => t2 match {
          case InputTactic(n2, i2) if n1 == n2 && i1 == i2 =>
            (ReplacementBelleContext(t1), Map[BelleDot, BelleExpr](), Map[BelleDot, BelleExpr]())
          case SeqTactic(n2l :: n2r) if t1 == n2l =>
            val p = new BelleDot()
            (ReplacementBelleContext(SeqTactic(t1, p)), Map(p -> TactixLibrary.nil), Map(p -> SeqTactic(n2r)))
          case _ =>
            val p = new BelleDot()
            (ReplacementBelleContext(p), Map(p -> t1), Map(p -> t2))
        }
      case DefTactic(n1, i1) => t2 match {
          case DefTactic(n2, i2) if n1 == n2 =>
            val d = diff(i1, i2)
            (ReplacementBelleContext(DefTactic(n1, d._1.t)), d._2, d._3)
        }
      case ApplyDefTactic(i1) => t2 match {
          case ApplyDefTactic(i2) =>
            val d = diff(i1, i2)
            (ReplacementBelleContext(ApplyDefTactic(d._1.t.asInstanceOf[DefTactic])), d._2, d._3)
        }
    }) ensures (r => r._1(r._2) === t1 && r._1(r._3) === t2, "Reapplying context expected to produce original tactics")
}
