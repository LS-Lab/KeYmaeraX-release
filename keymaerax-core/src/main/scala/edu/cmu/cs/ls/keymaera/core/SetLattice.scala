/**
 * Set Lattices.
 * @author smitsch
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaera.core

// require favoring immutable Seqs for soundness (probably)

import scala.collection.immutable

import scala.collection.GenTraversableOnce


/**
 * Lattice of sets, i.e. the lattice of sets that also includes top and top-like elements.
 * @tparam A Type of elements in the set
 * @author smitsch
 * @author aplatzer
 */
sealed trait SetLattice[A] {
  //@todo isInfinite might be a better name? If needed at all.
  def isTop: Boolean
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
      case os: TopSet[A] => ts.intersect(os.excluded).isEmpty /* this is a subset of that top if that doesn't exclude any of this */
    }
    case ts: TopSet[A] => other match {
      case FiniteLattice(_) => false           /* top not a subset of anything else */
      case os: TopSet[A] => os.excluded.subsetOf(ts.excluded) /* this top is a subset of that top if that excluded at most this's excluded */

    }
  }
  /** Set union */
  def ++(other: SetLattice[A]): SetLattice[A] = other match {
    case FiniteLattice(os) => this ++ os
    case os: TopSet[A] => this match {
      case FiniteLattice(ts) => os ++ ts   // commute ++ for type reasons
      case ts: TopSet[A] => new TopSet(ts.excluded.intersect(os.excluded), ts.symbols ++ os.symbols)
    }
  }
  def --(other: SetLattice[A]): SetLattice[A] = other match {
    case FiniteLattice(os) => this -- os
    case os: TopSet[A] => this match {
      case FiniteLattice(ts) => FiniteLattice(ts.intersect(os.excluded)) /* ts -- (top except os) == ts/\os */
      case ts: TopSet[A] => new TopSet(os.excluded -- ts.excluded, ts.symbols -- os.symbols)
    }
  }

  def intersect(other: SetLattice[A]): SetLattice[A] = other match {
    case FiniteLattice(os) => intersect(os)
    case os: TopSet[A] => this match {
        //@todo could do symmetric call as well: os.intersect(ts)
      case FiniteLattice(ts) => FiniteLattice(ts -- os.excluded) /* ts /\ (top except os) == ts--os */
      case ts: TopSet[A] => new TopSet(ts.excluded ++ os.excluded, ts.symbols.intersect(os.symbols)) /* (top except ts) /\ (top except os) == (top except ts++os) */

    }
  }
}

object SetLattice {
  def apply[A](e: A): SetLattice[A] = new FiniteLattice(Set(e))
  //def apply[A](e: A*): SetLattice[A] = new FiniteLattice(e.toSet)
  def apply[A](s: immutable.Set[A]): SetLattice[A] = new FiniteLattice(s)
  def apply[A](s: immutable.Seq[A]): SetLattice[A] = new FiniteLattice(s.toSet)
  def bottom[A]: SetLattice[A] = new FiniteLattice(Set.empty[A])
  def top[A](topSymbols: A*): SetLattice[A] = new TopSet(Set.empty, topSymbols.toSet)
  //@todo careful: this is an overapproximation of V\cup V'
  def topVarsDiffVars[A >: NamedSymbol](topSymbols: A*): SetLattice[A] = new TopSet(Set(DotTerm, DotFormula), topSymbols.toSet)

  /**
   * Only applies if sl isTop.
   * @param sl A SetLattice of NamedSymbols.
   * @return sl ++ sl' where sl' is the lattice containing the primes of the variables of sl.
   */
  def extendToDifferentialSymbols(sl : SetLattice[NamedSymbol]) : SetLattice[NamedSymbol] = {
    assert(sl isTop, "Cannot extend to differentialSymbols unless sl isTop.")
    val diffSymbols: Set[NamedSymbol] =
      sl.toSymbolSet
        .filter(_.isInstanceOf[Variable])
        .map(x => DifferentialSymbol(x.asInstanceOf[Variable]))
    sl ++ SetLattice(diffSymbols)
  }
}

/**
 * A finite element of a lattice, represented as a finite set of concrete elements.
 * @param set the concrete members of this finite element of a lattice
 * @tparam A Type of elements in the set
 * @note Implementation forwards to set.
 * @author aplatzer
 */
private case class FiniteLattice[A](set: immutable.Set[A])
  extends SetLattice[A] {
  def isTop = false
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
 * Represents top in a lattice of sets (i.e., includes all elements, except explicitly excluded ones). Additionally,
 * keeps track of which symbols specifically are named to be included (i.e., a program constant c, which in terms of
 * fv/bv variables represents all possible symbols and thus is top, is tracked as c in symbols).
 * @param excluded The elements not included in top.
 * @param symbols The specific symbols contained verbatim in the set, even if all except excluded are present.
 * @tparam A The type of elements.
 * @author smitsch
 * @todo CoSet may be a better name because it's a complement of a set.
 */
private case class TopSet[A](excluded: immutable.Set[A], symbols: immutable.Set[A])
  extends SetLattice[A] {
  def isTop = true
  def isEmpty = false
  /* top contains everything that's not excluded */
  def contains(e: A): Boolean = !excluded.contains(e)

  /* top excludes one element less now */
  def +(e: A): TopSet[A] = new TopSet(excluded - e, symbols + e)
  def ++(other: immutable.Set[A]): TopSet[A] = new TopSet(excluded -- other, symbols ++ other)
  def ++(other: GenTraversableOnce[A]): TopSet[A] = new TopSet(excluded -- other, symbols ++ other)
  /* union: (top except ts) ++ (top except os) == (top except ts/\os) */
  //def ++(other: TopSet[A]): TopSet[A] = new TopSet(excluded.intersect(other.excluded), symbols ++ other.symbols)
  /* top now excludes one more element */
  def -(e: A): TopSet[A] = new TopSet(excluded + e, symbols - e)
  def --(other: immutable.Set[A]): TopSet[A] = new TopSet(excluded ++ other, symbols -- other)
  def --(other: GenTraversableOnce[A]): TopSet[A] = new TopSet(excluded ++ other, symbols -- other)
  /* setminus: (top except ts) -- (top except os) == os -- ts */
  //def --(other: TopSet[A]): immutable.Set[A] = other.excluded -- excluded
  /* this top is a subset of that top if that excluded at most this's excluded */
  //def subsetOf(other: TopSet[A]): Boolean = other.excluded.subsetOf(excluded)
  /* (top except ts) /\ (top except os) == (top except ts++os) */
  //def intersect(other: TopSet[A]): TopSet[A] = new TopSet(excluded ++ other.excluded, symbols.intersect(other.symbols))
  def intersect(other: immutable.Set[A]): SetLattice[A] = TopSet(other -- excluded, symbols.intersect(other)) /* (top except ts) /\ os == os--ts */

  def map[B](fun: A => B): TopSet[B] = new TopSet(excluded.map(fun), symbols.map(fun))

  def toSetLattice[B >: A]: SetLattice[B] = new TopSet(excluded.toSet, symbols.toSet)
  def toSet[B >: A]: Set[B] = throw new IllegalStateException("SetLattice.top has no set representation")
  def toSymbolSet[B >: A]: Set[B] = symbols.toSet

  override def toString: String = "top except " + excluded.toString
  def prettyString: String = "top except {" + excluded.mkString(",") + "}"
}



