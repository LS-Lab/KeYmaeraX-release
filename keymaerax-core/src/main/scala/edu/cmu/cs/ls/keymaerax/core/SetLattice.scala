/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Set Lattices are lattice of finite or cofinite sets.
 * @author smitsch
 * @note Code Review: 2016-03-09
 */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness (probably)

import scala.collection.immutable

import scala.collection.GenTraversableOnce


/**
 * Lattice of sets, i.e. the lattice of sets that also includes top and top-like elements.
 *
 * @tparam A Type of elements in the set
 * @author smitsch
 * @author Andre Platzer
 */
sealed trait SetLattice[A] {
  def isInfinite: Boolean
  def isEmpty: Boolean

  // element operations
  def contains(elem: A): Boolean

  /** Return the set lattice including the extra element `elem` */
  def +(elem: A): SetLattice[A]
  /** Return the set lattice with the element `elem` removed */
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

  /** Convert to SetLattices of subtype parameters. */
  def toSetLattice[B >: A]: SetLattice[B]
  /** Convert to a (finite ordinary) Set if !isInfinite */
  def toSet[B >: A]: Set[B]
  /** Set of verbatim occurring symbols in this (possibly top) SetLattice */
  def symbols[B >: A]: Set[B]

  def prettyString: String

  // binary operations with mixed cases

  /* Subset of */
  def subsetOf(other: SetLattice[A]): Boolean = (this, other) match {
    case (FiniteSet(ts), FiniteSet(os)) => ts.subsetOf(os)
    case (FiniteSet(ts), os: CoFiniteSet[A]) => ts.intersect(os.excluded).isEmpty /* this is a subset of that top if that doesn't exclude any of this */
    case (ts: CoFiniteSet[A], FiniteSet(_)) => false           /* infinite sets are not a subset of any finite set */
    case (ts: CoFiniteSet[A], os: CoFiniteSet[A]) => os.excluded.subsetOf(ts.excluded) /* this coset is a subset of that coset if that excluded at most this's excluded */
  }
  /** Set union */
  def ++(other: SetLattice[A]): SetLattice[A] = { (this, other) match {
    case (_, FiniteSet(os)) => this ++ os  // ++(GenTraversableOnce[A])
    case (FiniteSet(ts), os: CoFiniteSet[A]) => os ++ ts   // commute to ++(GenTraversableOnce[A])
    case (ts: CoFiniteSet[A], os:CoFiniteSet[A]) => new CoFiniteSet(ts.excluded.intersect(os.excluded), ts.symbols ++ os.symbols)  // union of cosets is intersection of exceptions
  } } ensuring(r => this.subsetOf(r) && other.subsetOf(r), "set union has both constituents as subsets")

  /** Set subtraction */
  def --(other: SetLattice[A]): SetLattice[A] = {(this, other) match {
    case (_, FiniteSet(os)) => this -- os   // --(GenTraversableOnce[A])
    case (FiniteSet(ts), os: CoFiniteSet[A]) => FiniteSet(ts.intersect(os.excluded))  /* ts -- (all except os) == ts/\os, subtract everything but excluded, so retain excluded */
    case (ts: CoFiniteSet[A], os: CoFiniteSet[A]) => FiniteSet(os.excluded -- ts.excluded)      /* (all \ t) \ (all \ o) == o \ t, t was excluded and all except o were then removed */
  } } ensuring(r => r.subsetOf(this) && r.intersect(other).isEmpty, "set subtraction gives less")

  /** Set intersection */
  def intersect(other: SetLattice[A]): SetLattice[A] = { (this, other) match {
    case (_, FiniteSet(os)) => intersect(os)
    //@note could do symmetric call as well: os.intersect(ts)
    case (FiniteSet(ts), os: CoFiniteSet[A]) => FiniteSet(ts -- os.excluded) /* ts /\ (all except os) == ts--os, only exclusions disappear upon intersection with infinite sets */
    case (ts: CoFiniteSet[A], os: CoFiniteSet[A]) => new CoFiniteSet(ts.excluded ++ os.excluded, ts.symbols.intersect(os.symbols)) /* (top except ts) /\ (top except os) == (top except ts++os), intersection of cosetsd is union of exceptions */
  } } ensuring( r=> r.subsetOf(this) && r.subsetOf(other), "intersections are subsets of both constituents")
}


object SetLattice {
  def apply[A](e: A): SetLattice[A] = new FiniteSet(Set(e))
  //def apply[A](e: A*): SetLattice[A] = new FiniteSet(e.toSet)
  def apply[A](s: immutable.Set[A]): SetLattice[A] = new FiniteSet(s)
  def apply[A](s: immutable.Seq[A]): SetLattice[A] = new FiniteSet(s.toSet)
  def bottom[A]: SetLattice[A] = new FiniteSet(Set.empty[A])
  //def top[A](topSymbols: A*): SetLattice[A] = new CoFiniteSet(Set.empty, topSymbols.toSet)
  //@note this is an overapproximation of V\cup V'
  //@note all DotTerms are the same, regardless of their projection and sort (see DotTerm)
  def topVarsDiffVars[A >: NamedSymbol](): SetLattice[A] = new CoFiniteSet(Set(DotTerm, DotFormula), Set.empty)

  /**
   * Symbols and differential symbols of set lattice sl.
   * Will leave all Function and ProgramConst and DifferentialProgramConst in sl untouched
   * but add DifferentialSymbol for all Variables in sl.
   * @param sl A SetLattice of NamedSymbols.
   * @return sl ++ sl' where sl' is the lattice containing the primes of the variables in sl.
   */
  def extendToDifferentialSymbols(sl : SetLattice[NamedSymbol]) : SetLattice[NamedSymbol] = sl match {
    case FiniteSet(set) => FiniteSet(extendToDifferentialSymbols(set))
    case CoFiniteSet(excluded, symbols) if !excluded.exists(x=>x.isInstanceOf[DifferentialSymbol]) =>
      //@note if no differential symbols were excluded (such as in V\cup V' or topVarsDiffVars),
      //@note then the lattice is already closed under ' so only literal symbols are augmented with '
      CoFiniteSet(excluded, extendToDifferentialSymbols(symbols))
    case sl:CoFiniteSet[NamedSymbol] =>
      assert(false, "Extension to differentialSymbols are not yet implemented if sl isInfinite: " + sl); ???
  }

  /**
   * Symbols and differential symbols of set.
 *
   * @param set A Set of NamedSymbols.
   * @return set ++ set' where set' is the set containing the primes of the variables in set.
   */
  def extendToDifferentialSymbols(set : Set[NamedSymbol]) : Set[NamedSymbol] =
    set ++ set.filter(_.isInstanceOf[Variable]).map(x => DifferentialSymbol(x.asInstanceOf[Variable]))
}

/**
 * A finite element of a lattice, represented as a finite set of concrete elements.
 *
 * @param set the concrete members of this finite element of a lattice
 * @tparam A Type of elements in the set
 * @note Implementation forwards to set.
 * @author Andre Platzer
 */
private case class FiniteSet[A](set: immutable.Set[A]) extends SetLattice[A] {
  def isInfinite = false
  def isEmpty: Boolean = set.isEmpty

  // directly forward to representing set

  def contains(elem: A): Boolean = set.contains(elem)

  def +(elem: A): SetLattice[A] = FiniteSet(set + elem)
  def -(elem: A): SetLattice[A] = FiniteSet(set - elem)
  def ++(other: GenTraversableOnce[A]): SetLattice[A] = FiniteSet(set ++ other)
  def --(other: GenTraversableOnce[A]): SetLattice[A] = FiniteSet(set -- other)
  def intersect(other: immutable.Set[A]): SetLattice[A] = FiniteSet(set.intersect(other))

  def map[B](fun: A => B): SetLattice[B] = FiniteSet(set.map(fun))

  override def toString: String = set.toString()
  def prettyString: String = "{" + set.mkString(",") + "}"

  def toSetLattice[B >: A]: SetLattice[B] = FiniteSet(toSet)
  def toSet[B >: A]: Set[B] = set.toSet

  def symbols[B >: A]: Set[B] = toSet
}

/**
 * Represents a co-set i.e. an infinite set that is the complement of a finite set.
 * It includes all elements, except explicitly excluded ones. Additionally,
 * keeps track of which symbols specifically are named to be included (i.e., a program constant c, which in terms of
 * fv/bv variables represents all possible symbols and thus is top, is tracked as c in symbols).
 *
 * @param excluded The elements not included in top.
 * @param literally The specific symbols contained verbatim in the set, even if all except excluded are present.
 * @tparam A The type of elements.
 * @author smitsch
 */
private case class CoFiniteSet[A](excluded: immutable.Set[A], literally: immutable.Set[A]) extends SetLattice[A] {
  def isInfinite = true
  def isEmpty = false
  /* Cosets contain everything that's not excluded */
  def contains(e: A): Boolean = !excluded.contains(e)

  /* Coset excludes one element less now */
  def +(e: A): CoFiniteSet[A] = new CoFiniteSet(excluded - e, literally + e)
  def ++(other: GenTraversableOnce[A]): CoFiniteSet[A] = new CoFiniteSet(excluded -- other, literally ++ other)
  /* top now excludes one more element */
  def -(e: A): CoFiniteSet[A] = new CoFiniteSet(excluded + e, literally - e)
  def --(other: GenTraversableOnce[A]): CoFiniteSet[A] = new CoFiniteSet(excluded ++ other, literally -- other)
  def intersect(other: immutable.Set[A]): SetLattice[A] = FiniteSet(other -- excluded)   /* (all except ts) /\ os == os--ts */

  def map[B](fun: A => B): CoFiniteSet[B] = new CoFiniteSet(excluded.map(fun), literally.map(fun))

  def toSetLattice[B >: A]: SetLattice[B] = new CoFiniteSet(excluded.toSet, literally.toSet)
  def toSet[B >: A]: Set[B] = throw new IllegalStateException("CoSets are infinite so have no finite Set representation")
  def symbols[B >: A]: Set[B] = literally.toSet

  override def toString: String = "all but " + excluded.toString
  def prettyString: String = "all but {" + excluded.mkString(",") + "}"
}



