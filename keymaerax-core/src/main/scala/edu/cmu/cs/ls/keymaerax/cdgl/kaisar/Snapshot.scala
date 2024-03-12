/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * A snapshot associates subscripts to variable names. Because indices are used in SSA to distinguish the values of one
 * variable at different points in time or different points in the code, a snapshot suffices as an abstraction for
 * different "times" (technically, locations) in a proof.
 *
 * @author
 *   Brandon Bohrer
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.cdgl.kaisar.SSAPass]]
 */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.{Ident, Subscript}
import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.ProofTraversal.TraversalFunction
import edu.cmu.cs.ls.keymaerax.core._

case class Snapshot(private val m: Map[String, Subscript]) {

  /** Entry (x -> None) means we saw base variable "x", whereas no "x" entry means we never saw any version of "x". */
  val asMap: Map[String, Subscript] = m

  /** Collapse Some(None) to None */
  private def opt[T](x: Option[Option[T]]): Option[T] = x match {
    case None => None
    case Some(None) => None
    case Some(Some(x)) => Some(x)
  }

  /**
   * Add an element x to the map, and override any previous index of x. In contrast, the public interface for
   * [[Snapshot]] should take the maximum index rather than forgetting the old index for x.
   */
  private def +(x: (String, Subscript)): Snapshot = Snapshot(m.+(x))

  /** Look up "x" but distinguish the "never saw x" case (None) vs "only saw x with no index" case (Some(None)) */
  def getOpt(s: String): Option[Subscript] = m.get(s)

  /**
   * Look up "x" and don't distinguish the "never saw x" case. This can be more convenient, and is adequate so long as
   * we wish for SSA numbering to start at x_0 rather than x.
   */
  def get(s: String): Subscript = opt(getOpt(s))
  def contains(s: String): Boolean = getOpt(s).isDefined

  /* The following functions wrap the underlying Map[T1, T2] methods. */
  def keySet: Set[String] = m.keySet
  def filter(p: ((String, Subscript)) => Boolean): Snapshot = Snapshot(m.filter(p))

  /** Take the union of two snapshots. When both snapshots mention the same variable, the greater subscript is kept. */
  def ++(other: Snapshot): Snapshot = {
    val keys: Set[String] = keySet.++(other.keySet)
    keys.foldLeft[Snapshot](Snapshot.empty)((map, k) =>
      (opt(getOpt(k)), opt(other.getOpt(k))) match {
        case (Some(x: Int), Some(y: Int)) => map.+(k -> Some(x.max(y)))
        case (x: Some[Int], _) => map.+(k -> x)
        case (_, y: Some[Int]) => map.+(k -> y)
        case _ => map
      }
    )
  }

  /** Augment snapshot with all variables freshly bound in the pattern. */
  /* @TODO: Double-check that the snapshot captures all previous free appearances of variables and not just bound
   * appearances. Otherwise, we might treat a variable in a pattern as a binder when it should be a free mention. */
  def addPattern(pat: Expression): Snapshot = {
    // A pattern only binds a variable if it has not been mentioned before. So select just the "new" variables.
    val bv = keySet.map(Variable(_))
    val fv = pat match {
      case f: Term => StaticSemantics(f)
      case fml: Formula => StaticSemantics(fml).fv
      case hp: Program => StaticSemantics(hp).fv
    }
    val fresh: Set[Variable] = fv.toSet.--(bv)
    val freshSet = fresh.foldLeft[Set[(String, Option[Int])]](Set())((acc, x) => acc.+((x.name, Some(0))))
    Snapshot(freshSet.toMap)
  }

  /**
   * Add a set of bound variables to a snapshot. This (or increment) should be called wherever variables are assigned.
   * If the variables have been bound before, their subscripts are increased according to SSA.
   */
  def addSet(vars: Set[Variable]): Snapshot = {
    val allVars: Set[String] = keySet.++(vars.map(_.name))
    allVars.foldLeft[Snapshot](Snapshot.empty) { case (snap, v) =>
      // keep elements which were only in keySet but not vars
      if (!vars.contains(Variable(v))) (snap.+(v -> get(v)))
      else {
        val idx = opt(getOpt(v)) match {
          case None => Some(0)
          case Some(i) => Some(i + 1)
        }
        snap.+(v -> idx)
      }
    }
  }

  /** Input should be in SSA form already. Call this on every variable to reconstruct Snapshot from output of SSA. */
  def revisit(x: Variable): Snapshot = {
    x match {
      case BaseVariable(name, opt, _) =>
        val index = (opt, getOpt(name)) match {
          case (_, None) => opt
          case (None, Some(x)) => x
          case (x, Some(None)) => x
          case (Some(i), Some(Some(j))) => Some(i.max(j))
        }
        this.+(name -> index)
      case DifferentialSymbol(bv) => revisit(bv)
    }
  }

  /**
   * Add a variable to a snapshot. This (or addSet) should be called wherever a single variable is assigned. If [[x]] is
   * already in the snapshot, its subscript is incremented.
   * @return
   *   the variable with its new index and the updated snapshot.
   */
  def increment(x: Variable): (Variable, Snapshot) = {
    x match {
      case BaseVariable(name, Some(_), sort) =>
        throw new Exception("SSA pass expected no subscripted variables in input")
      case BaseVariable(name, None, sort) =>
        val index: Option[Int] = getOpt(name) match {
          case None => Some(0)
          case Some(None) => Some(0)
          case Some(Some(i)) => Some(i + 1)
        }
        val snap = this.+(name -> index)
        (BaseVariable(name, index, sort), snap)
      case DifferentialSymbol(bv) =>
        val (v, snap) = increment(x)
        (DifferentialSymbol(v), snap)
    }
  }

  /** @return whether every key has same or higher subscript in other snapshot */
  def <=(other: Snapshot): Boolean = {
    if (!m.keySet.subsetOf(other.keySet)) return false
    m.forall({
      case (x, None) => true
      case (x, Some(i)) => other.get(x).exists(i <= _)
    })
  }
}

object Snapshot {
  val empty: Snapshot = new Snapshot(Map())
  def initial(v: Set[Ident]): Snapshot = new Snapshot(v.map(v => (v.name, Some(0))).toMap)
  def ofContext(c: Context): Snapshot = {
    val vs = VariableSets(c)
    val vars = vs.freeVars ++ vs.boundVars
    var snap = Snapshot.initial(vars)
    val tf = new TraversalFunction {
      override def postS(kc: Context, kce: Context, s: Statement): Statement = {
        s match {
          case fr: For => snap = snap.revisit(fr.metX); fr
          case fr: ForProgress => snap = snap.revisit(fr.forth.metX); fr
          case mod: Modify => mod.mods.foreach({ case (x, f) => snap = snap.revisit(x) }); mod
          case s => s
        }
      }

      override def postDiffS(kc: Context, kce: Context, s: DiffStatement): DiffStatement = {
        s match {
          case AtomicODEStatement(AtomicODE(DifferentialSymbol(x), _), _) => snap = snap.revisit(x); s
          case _ => s
        }
      }

      override def postDomS(kc: Context, kce: Context, s: DomainStatement): DomainStatement = {
        s match {
          case DomModify(_id, x, f) => snap = snap.revisit(x); s
          case _ => s
        }
      }
    }
    ProofTraversal.traverse(Context.empty, Context.empty, c.s, tf)
    snap
  }
}
