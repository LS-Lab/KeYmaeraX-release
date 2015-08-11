/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Set Lattices.
 * @author smitsch
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness (probably)

import scala.collection.immutable

import scala.collection.GenTraversableOnce


/**
 * Lattice of sets, i.e. the lattice of sets that also includes top and top-like elements.
 * @tparam A Type of elements in the set
 * @author smitsch
 * @author Andre Platzer
 */
sealed trait SetLattice[A] {
  def isInfinite: Boolean
  def isEmpty: Boolean

  // element operations
  def contains(elem: A): Boolean

  def +(elem: A): SetLattice[A]
  def -(elem: A): SetLattice[A]

  // set operations

  /** Set union */
  def ++(other: GenTraversableOnce[A]): SetLattice[A]
  /** Set subtraction */
  def --(other: GenTraversableOnce[A]): SetLattice[A]
  def intersect(other: immutable.Set[A]): SetLattice[A]

  // conversions and mappings
  def map[B](fun: A => B): SetLattice[B]

  def toSetLattice[B >: A]: SetLattice[B]
  def toSet[B >: A]: Set[B]
  /** Set of verbatim occurring symbols in this (possibly top) SetLattice */
  def toSymbolSet[B >: A]: Set[B]

  def prettyString: String

  // binary operations with mixed cases

  def subsetOf(other: SetLattice[A]): Boolean = this match {
    case FiniteLattice(ts) => other match {
      case FiniteLattice(os) => ts.subsetOf(os)
      case os: CoSet[A] => ts.intersect(os.excluded).isEmpty /* this is a subset of that top if that doesn't exclude any of this */
    }
    case ts: CoSet[A] => other match {
      case FiniteLattice(_) => false           /* top not a subset of anything else */
      case os: CoSet[A] => os.excluded.subsetOf(ts.excluded) /* this top is a subset of that top if that excluded at most this's excluded */

    }
  }
  /** Set union */
  def ++(other: SetLattice[A]): SetLattice[A] = other match {
    case FiniteLattice(os) => this ++ os
    case os: CoSet[A] => this match {
      case FiniteLattice(ts) => os ++ ts   // commute ++ for type reasons
      case ts: CoSet[A] => new CoSet(ts.excluded.intersect(os.excluded), ts.symbols ++ os.symbols)
    }
  }
  def --(other: SetLattice[A]): SetLattice[A] = other match {
    case FiniteLattice(os) => this -- os
    case os: CoSet[A] => this match {
      case FiniteLattice(ts) => FiniteLattice(ts.intersect(os.excluded)) /* ts -- (top except os) == ts/\os */
      case ts: CoSet[A] => new CoSet(os.excluded -- ts.excluded, ts.symbols -- os.symbols)
    }
  }

  def intersect(other: SetLattice[A]): SetLattice[A] = other match {
    case FiniteLattice(os) => intersect(os)
    case os: CoSet[A] => this match {
        //@note could do symmetric call as well: os.intersect(ts)
      case FiniteLattice(ts) => FiniteLattice(ts -- os.excluded) /* ts /\ (top except os) == ts--os */
      case ts: CoSet[A] => new CoSet(ts.excluded ++ os.excluded, ts.symbols.intersect(os.symbols)) /* (top except ts) /\ (top except os) == (top except ts++os) */

    }
  }
}

object SetLattice {
  def apply[A](e: A): SetLattice[A] = new FiniteLattice(Set(e))
  //def apply[A](e: A*): SetLattice[A] = new FiniteLattice(e.toSet)
  def apply[A](s: immutable.Set[A]): SetLattice[A] = new FiniteLattice(s)
  def apply[A](s: immutable.Seq[A]): SetLattice[A] = new FiniteLattice(s.toSet)
  def bottom[A]: SetLattice[A] = new FiniteLattice(Set.empty[A])
  def top[A](topSymbols: A*): SetLattice[A] = new CoSet(Set.empty, topSymbols.toSet)
  //@note this is an overapproximation of V\cup V'
  def topVarsDiffVars[A >: NamedSymbol](topSymbols: A*): SetLattice[A] = new CoSet(Set(DotTerm, DotFormula), topSymbols.toSet)

  /**
   * Symbols and differential symbols of set lattice sl.
   * @param sl A SetLattice of NamedSymbols.
   * @return sl ++ sl' where sl' is the lattice containing the primes of the variables in sl.
   */
  def extendToDifferentialSymbols(sl : SetLattice[NamedSymbol]) : SetLattice[NamedSymbol] = sl match {
    case CoSet(excluded, symbols) if excluded == topVarsDiffVars().asInstanceOf[CoSet[NamedSymbol]].excluded =>
      // V\cup V' already closed under adding '.
      //@note Its overapproximation topVarsDiffVars is also closed since DotTerm, DotFormula are not variables
      CoSet(excluded, extendToDifferentialSymbols(symbols))
    case FiniteLattice(set) => SetLattice(extendToDifferentialSymbols(set))
    case sl:CoSet[NamedSymbol] =>
      assert(false, "Extension to differentialSymbols are not yet implemented if sl isInfinite: " + sl); ???
  }

  /**
   * Symbols and differential symbols of set.
   * @param set A Set of NamedSymbols.
   * @return set ++ set' where set' is the set containing the primes of the variables in set.
   */
  def extendToDifferentialSymbols(set : Set[NamedSymbol]) : Set[NamedSymbol] = set ++
    set.filter(_.isInstanceOf[Variable]).map(x => DifferentialSymbol(x.asInstanceOf[Variable]))
}

/**
 * A finite element of a lattice, represented as a finite set of concrete elements.
 * @param set the concrete members of this finite element of a lattice
 * @tparam A Type of elements in the set
 * @note Implementation forwards to set.
 * @author Andre Platzer
 */
private case class FiniteLattice[A](set: immutable.Set[A])
  extends SetLattice[A] {
  def isInfinite = false
  def isEmpty: Boolean = set.isEmpty

  def contains(elem: A): Boolean = set.contains(elem)

  def +(elem: A): SetLattice[A] = FiniteLattice(set + elem)
  def -(elem: A): SetLattice[A] = FiniteLattice(set - elem)
  def ++(other: GenTraversableOnce[A]): SetLattice[A] = FiniteLattice(set ++ other)
  def --(other: GenTraversableOnce[A]): SetLattice[A] = FiniteLattice(set -- other)
  def intersect(other: immutable.Set[A]): SetLattice[A] = FiniteLattice(set.intersect(other))

  def map[B](fun: A => B): SetLattice[B] = FiniteLattice(set.map(fun))

  override def toString: String = set.toString()
  def prettyString: String = "{" + set.mkString(",") + "}"

  def toSetLattice[B >: A]: SetLattice[B] = FiniteLattice(toSet)
  def toSet[B >: A]: Set[B] = toSymbolSet
  def toSymbolSet[B >: A]: Set[B] = set.toSet
}

/**
 * Represents a co-set i.e. an infinite set that is the complement of a finite set.
 * It includes all elements, except explicitly excluded ones. Additionally,
 * keeps track of which symbols specifically are named to be included (i.e., a program constant c, which in terms of
 * fv/bv variables represents all possible symbols and thus is top, is tracked as c in symbols).
 * @param excluded The elements not included in top.
 * @param symbols The specific symbols contained verbatim in the set, even if all except excluded are present.
 * @tparam A The type of elements.
 * @author smitsch
 */
private case class CoSet[A](excluded: immutable.Set[A], symbols: immutable.Set[A])
  extends SetLattice[A] {
  def isInfinite = true
  def isEmpty = false
  /* top contains everything that's not excluded */
  def contains(e: A): Boolean = !excluded.contains(e)

  /* top excludes one element less now */
  def +(e: A): CoSet[A] = new CoSet(excluded - e, symbols + e)
  def ++(other: immutable.Set[A]): CoSet[A] = new CoSet(excluded -- other, symbols ++ other)
  def ++(other: GenTraversableOnce[A]): CoSet[A] = new CoSet(excluded -- other, symbols ++ other)
  /* top now excludes one more element */
  def -(e: A): CoSet[A] = new CoSet(excluded + e, symbols - e)
  def --(other: immutable.Set[A]): CoSet[A] = new CoSet(excluded ++ other, symbols -- other)
  def --(other: GenTraversableOnce[A]): CoSet[A] = new CoSet(excluded ++ other, symbols -- other)
  def intersect(other: immutable.Set[A]): SetLattice[A] = FiniteLattice(other -- excluded)   /* (top except ts) /\ os == os--ts */

  def map[B](fun: A => B): CoSet[B] = new CoSet(excluded.map(fun), symbols.map(fun))

  def toSetLattice[B >: A]: SetLattice[B] = new CoSet(excluded.toSet, symbols.toSet)
  def toSet[B >: A]: Set[B] = throw new IllegalStateException("SetLattice.top has no set representation")
  def toSymbolSet[B >: A]: Set[B] = symbols.toSet

  override def toString: String = "all but " + excluded.toString
  def prettyString: String = "all but {" + excluded.mkString(",") + "}"
}



