package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.cdgl.kaisar.KaisarProof.Subscript
import edu.cmu.cs.ls.keymaerax.core._

case class Snapshot (private val m: Map[String, Subscript])  {
  val asMap: Map[String, Subscript] = m
  private def opt[T](x: Option[Option[T]]): Option[T] = x match {case None => None case Some(None) => None case Some(Some(x)) => Some(x)}
  def get(s: String): Option[Subscript] = m.get(s)
  def keySet: Set[String] = m.keySet
  def filter(p: ((String, Subscript)) => Boolean): Snapshot = Snapshot(m.filter(p))
  def +(x: (String, Subscript)): Snapshot = Snapshot(m.+(x))
  def ++(other: Snapshot): Snapshot = {
    val keys: Set[String] = keySet.++(other.keySet)
    keys.foldLeft[Snapshot](Snapshot.empty)((map, k) =>
      (opt(get(k)), opt(other.get(k))) match {
        case (Some(x: Int),Some(y: Int)) => map.+(k -> Some(x.max(y)))
        case (x: Some[Int], _) => map.+(k -> x)
        case (_, y: Some[Int]) => map.+(k -> y)
        case _ => map
      }
    )
  }

  def addPattern(pat: Expression): Snapshot = {
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

  def addSet(vars: Set[Variable]): Snapshot = {
    val allVars: Set[String] = keySet.++(vars.map(_.name))
    allVars.foldLeft[Snapshot](Snapshot.empty){case (snap, v) =>
      val idx = opt(get(v)) match {case None => Some(0) case Some(i) => Some(i+1)}
      snap.+(v -> idx)
    }
  }

  def increment(x: Variable): (Variable, Snapshot) = {
    x match {
      case BaseVariable(name, Some(_), sort) => throw new Exception("SSA pass expected no subscripted variables in input")
      case BaseVariable(name, None, sort) =>
        val index: Option[Int] = get(name) match {
          case None => Some(0)
          case Some(None) => Some(0)
          case Some(Some(i)) => Some(i+1)
        }
        val snap = this.+(name -> index)
        (BaseVariable(name, index, sort), snap)
      case DifferentialSymbol(bv) =>
        val (v, snap) = increment(x)
        (DifferentialSymbol(v), snap)
    }
  }
}
object Snapshot {
  val empty: Snapshot = new Snapshot(Map())
}

