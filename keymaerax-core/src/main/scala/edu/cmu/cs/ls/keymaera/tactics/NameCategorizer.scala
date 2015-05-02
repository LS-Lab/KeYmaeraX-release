package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._

import scala.collection.immutable.Set

/**
 * Static access to functions of Substitution.
 * @author Stefan Mitsch
 */
object NameCategorizer {
  /** Returns the set of names maybe free in term t (same as certainly free). */
  def maybeFreeVariables(t: Term): Set[NamedSymbol] = StaticSemantics(t).toSet /*match {
    case Right(ts) => ts
    case Left(_) => throw new IllegalArgumentException(s"Unexpected term $t: any variable is free")
  }*/
  /** Returns the set of names maybe free in formula f. */
  def maybeFreeVariables(f: Formula): Set[NamedSymbol] = StaticSemantics(f).fv.toSet /*match {
    case Right(ts) => ts
    case Left(_) => throw new IllegalArgumentException(s"Unexpected formula $f: any variable is free")
  }*/
  /** Returns the set of names maybe free in program p. */
  def maybeFreeVariables(p: Program): Set[NamedSymbol] = StaticSemantics(p).fv.toSet  /*match {
    case Right(ts) => ts
    case Left(_) => throw new IllegalArgumentException(s"Unexpected program $p: any variable is free")
  }*/
  /** Returns the set of names certainly free in program p. */
  def freeVariables(p: Program): Set[NamedSymbol] = {
    val ba = StaticSemantics(p)
    (ba.fv -- (ba.mbv ++ ba.bv)).toSet /*.s match {
      case Right(ts) => ts
      case Left(_) => throw new IllegalArgumentException(s"Unexpected program $p: any variable is free")
    }*/
  }
  /** Returns the set of names certainly free in formula f. */
  def freeVariables(f: Formula) = {
    val ba = StaticSemantics(f)
    (ba.fv -- ba.bv).toSet /*s match {
      case Left(_) => throw new IllegalArgumentException(s"Unexpected formula $f: any variable imaginable is free")
      case Right(ts) => ts
    }*/
  }
  /** Returns the set of names maybe bound in program p. */
  def maybeBoundVariables(p: Program): Set[NamedSymbol] = StaticSemantics(p).bv.toSet /*s match {
    case Right(ts) => ts
    case Left(_) => throw new IllegalArgumentException(s"Unexpected program $p: all variables are bound")
  }*/
}
