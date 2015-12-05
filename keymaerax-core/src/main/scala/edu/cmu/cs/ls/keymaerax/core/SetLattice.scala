/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Set Lattices are lattice of finite or cofinite sets.
 * @author smitsch
 * @note Code Review: 2015-08-24
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
  /** Set intersection */
  def intersect(other: immutable.Set[A]): SetLattice[A]

  // conversions and mappings
  /** map a function over this SetLattice */
  def map[B](fun: A => B): SetLattice[B]

  def toSetLattice[B >: A]: SetLattice[B]
  /** Convert to a (finite ordinary) Set if !isInfinite */
  def toSet[B >: A]: Set[B]
  /** Set of verbatim occurring symbols in this (possibly top) SetLattice */
  def toSymbolSet[B >: A]: Set[B]

  def prettyString: String

  // binary operations with mixed cases

  /* Subset of */
  def subsetOf(other: SetLattice[A]): Boolean = this match {
    case FiniteLattice(ts) => other match {
      case FiniteLattice(os) => ts.subsetOf(os)
      case os: CoSet[A] => ts.intersect(os.excluded).isEmpty /* this is a subset of that top if that doesn't exclude any of this */
    }
    case ts: CoSet[A] => other match {
      case FiniteLattice(_) => false           /* infinite sets are not a subset of any finite set */
      case os: CoSet[A] => os.excluded.subsetOf(ts.excluded) /* this coset is a subset of that coset if that excluded at most this's excluded */
    }
  }
  /** Set union */
  def ++(other: SetLattice[A]): SetLattice[A] = { other match {
    case FiniteLattice(os) => this ++ os  // ++(GenTraversableOnce[A])
    case os: CoSet[A] => this match {
      case FiniteLattice(ts) => os ++ ts   // commute to ++(GenTraversableOnce[A])
      case ts: CoSet[A] => new CoSet(ts.excluded.intersect(os.excluded), ts.symbols ++ os.symbols)  // union of cosets is intersection of exceptions
    }
  } } ensuring(r => this.subsetOf(r) && other.subsetOf(r), "set union has both constituents as subsets")

  /** Set subtraction */
  def --(other: SetLattice[A]): SetLattice[A] = {other match {
    case FiniteLattice(os) => this -- os   // --(GenTraversableOnce[A])
    case os: CoSet[A] => this match {
      case FiniteLattice(ts) => FiniteLattice(ts.intersect(os.excluded))  /* ts -- (all except os) == ts/\os, subtract everything but excluded, so retain excluded */
      case ts: CoSet[A] => FiniteLattice(os.excluded -- ts.excluded)      /* (all \ t) \ (all \ o) == o \ t, t was excluded and all except o were then removed */
    }
  } } ensuring(r => r.subsetOf(this) && r.intersect(other).isEmpty, "set subtraction gives less")

  /** Set intersection */
  def intersect(other: SetLattice[A]): SetLattice[A] = { other match {
    case FiniteLattice(os) => intersect(os)
    case os: CoSet[A] => this match {
        //@note could do symmetric call as well: os.intersect(ts)
      case FiniteLattice(ts) => FiniteLattice(ts -- os.excluded) /* ts /\ (all except os) == ts--os, only exclusions disappear upon intersection with infinite sets */
      case ts: CoSet[A] => new CoSet(ts.excluded ++ os.excluded, ts.symbols.intersect(os.symbols)) /* (top except ts) /\ (top except os) == (top except ts++os), intersection of cosetsd is union of exceptions */

    }
  } } ensuring( r=> r.subsetOf(this) && r.subsetOf(other), "intersections are subsets of both constituents")
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
    case FiniteLattice(set) => SetLattice(extendToDifferentialSymbols(set))
    case CoSet(excluded, symbols) if !excluded.exists(x=>x.isInstanceOf[DifferentialSymbol]) =>
      //@note if no differential symbols were excluded (such as in V\cup V' or topVarsDiffVars),
      //@note then the lattice is already closed under ' so only literal symbols are augmented with '
      CoSet(excluded, extendToDifferentialSymbols(symbols))
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
private case class FiniteLattice[A](set: immutable.Set[A]) extends SetLattice[A] {
  def isInfinite = false
  def isEmpty: Boolean = set.isEmpty

  // directly forward to representing set

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
private case class CoSet[A](excluded: immutable.Set[A], symbols: immutable.Set[A]) extends SetLattice[A] {
  def isInfinite = true
  def isEmpty = false
  /* Cosets contain everything that's not excluded */
  def contains(e: A): Boolean = !excluded.contains(e)

  /* Coset excludes one element less now */
  def +(e: A): CoSet[A] = new CoSet(excluded - e, symbols + e)
  def ++(other: GenTraversableOnce[A]): CoSet[A] = new CoSet(excluded -- other, symbols ++ other)
  /* top now excludes one more element */
  def -(e: A): CoSet[A] = new CoSet(excluded + e, symbols - e)
  def --(other: GenTraversableOnce[A]): CoSet[A] = new CoSet(excluded ++ other, symbols -- other)
  def intersect(other: immutable.Set[A]): SetLattice[A] = FiniteLattice(other -- excluded)   /* (all except ts) /\ os == os--ts */

  def map[B](fun: A => B): CoSet[B] = new CoSet(excluded.map(fun), symbols.map(fun))

  def toSetLattice[B >: A]: SetLattice[B] = new CoSet(excluded.toSet, symbols.toSet)
  def toSet[B >: A]: Set[B] = throw new IllegalStateException("CoSets are infinite so have no finite Set representation")
  def toSymbolSet[B >: A]: Set[B] = symbols.toSet

  override def toString: String = "all but " + excluded.toString
  def prettyString: String = "all but {" + excluded.mkString(",") + "}"
}



