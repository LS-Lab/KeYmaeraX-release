/**
 * Set Lattices.
 * @author smitsch
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaera.core

// require favoring immutable Seqs for soundness (probably)

import scala.collection.immutable

import scala.collection.GenTraversableOnce


//  type SetLattice[A] = Set[A]
//  private def topExceptDotFormula[A]: Set[A] = ???
//  private def topExceptDotTerm[A]: Set[A] = ???

//object SetLattice {
//  def apply[A](e: A): Set[A] = Set(e)
//  def bottom[A]: Set[A] = Set()
//}

/**
 * Represents top in a lattice of sets (i.e., includes all elements, except explicitly excluded ones). Additionally,
 * keeps track of which symbols specifically are named to be included (i.e., a program constant c, which in terms of
 * fv/bv variables represents all possible symbols and thus is top, is tracked as c in symbols).
 * @param excluded The elements not included in top.
 * @param symbols The specific symbols contained verbatim in the set, even if all except excluded are present.
 * @tparam A The type of elements.
 */
private case class TopSet[A](excluded: immutable.Set[A], symbols: immutable.Set[A]) {
  /* top contains everything that's not excluded */
  def contains(e: A): Boolean = !excluded.contains(e)
  /* this top is a subset of that top if that excluded at most this's excluded */
  def subsetOf(other: TopSet[A]): Boolean = other.excluded.subsetOf(excluded)
  /* (top except ts) /\ (top except os) == (top except ts++os) */
  def intersect(other: TopSet[A]): TopSet[A] = new TopSet(excluded ++ other.excluded, symbols.intersect(other.symbols))
  /* top excludes one element less now */
  def +(e: A): TopSet[A] = new TopSet(excluded - e, symbols + e)
  def ++(other: immutable.Set[A]): TopSet[A] = new TopSet(excluded -- other, symbols ++ other)
  def ++(other: GenTraversableOnce[A]): TopSet[A] = new TopSet(excluded -- other, symbols ++ other)
  /* union: (top except ts) ++ (top except os) == (top except ts/\os) */
  def ++(other: TopSet[A]): TopSet[A] = new TopSet(excluded.intersect(other.excluded), symbols ++ other.symbols)
  /* top now excludes one more element */
  def -(e: A): TopSet[A] = new TopSet(excluded + e, symbols - e)
  def --(other: immutable.Set[A]): TopSet[A] = new TopSet(excluded ++ other, symbols -- other)
  def --(other: GenTraversableOnce[A]): TopSet[A] = new TopSet(excluded ++ other, symbols -- other)
  /* setminus: (top except ts) -- (top except os) == os -- ts */
  def --(other: TopSet[A]): immutable.Set[A] = other.excluded -- excluded

  def map[B](fun: A => B): TopSet[B] = new TopSet(excluded.map(fun), symbols.map(fun))
}

/**
 * Lattice of sets. Top includes all elements, except the ones listed. Bottom is the empty set.
 * @param s Elements in the set: Left[A] elements excluded from the set, Right[A] elements included in the set
 * @tparam A Type of elements in the set
 * @note s is private for abstraction purposes to be able to change representation.
 */
class SetLattice[A](private val s: Either[TopSet[A], immutable.Set[A]]) {
  def isTop = s.isLeft
  def isEmpty: Boolean = s match {
    case Right(ts) => ts.isEmpty
    case Left(_) => false /* top is never empty, no matter how much it excludes */
  }
  def contains(elem: A): Boolean = s match {
    case Right(ts) => ts.contains(elem)
    case Left(ts) => ts.contains(elem)
  }
  def subsetOf(other: SetLattice[A]): Boolean = s match {
    case Right(ts) => other.s match {
      case Right(os) => ts.subsetOf(os)
      case Left(os) => ts.intersect(os.excluded).isEmpty /* this is a subset of that top if that doesn't exclude any of this */
    }
    case Left(ts) => other.s match {
      case Right(_) => false           /* top not a subset of anything else */
      case Left(os) => ts.subsetOf(os)
    }
  }
  def intersect(other: immutable.Set[A]): SetLattice[A] = s match {
    case Right(ts) => SetLattice(ts.intersect(other))
    case Left(ts) => SetLattice(other -- ts.excluded)           /* (top except ts) /\ os == os--ts */
  }
  def intersect(other: SetLattice[A]): SetLattice[A] = other.s match {
    case Right(os) => intersect(os)
    case Left(os) => s match {
      case Right(ts) => SetLattice(ts -- os.excluded)           /* ts /\ (top except os) == ts--os */
      case Left(ts) => SetLattice(ts.intersect(os))
    }
  }

  def map[B](fun: A => B): SetLattice[B] = s match {
    case Right(ts) => SetLattice(ts.map(fun))
    case Left(ts) => SetLattice(ts.map(fun))
  }

  def +(elem: A): SetLattice[A] = s match {
    case Right(ts) => SetLattice(ts + elem)
    case Left(ts) => SetLattice(ts + elem)
  }
  def -(elem: A): SetLattice[A] = s match {
    case Right(ts) => SetLattice(ts - elem)
    case Left(ts) => SetLattice(ts - elem)
  }
  def ++(other: GenTraversableOnce[A]): SetLattice[A] = s match {
    case Right(ts) => SetLattice(ts ++ other)
    case Left(ts) => SetLattice(ts ++ other)
  }
  /** Set union */
  def ++(other: SetLattice[A]): SetLattice[A] = other.s match {
    case Right(os) => this ++ os
    case Left(os) => s match {
      case Right(ts) => SetLattice(os ++ ts)   // commute ++ for type reasons
      case Left(ts) => SetLattice(ts ++ os)
    }
  }

  /** Set subtraction */
  def --(other: GenTraversableOnce[A]): SetLattice[A] = s match {
    case Left(ts) => SetLattice(ts -- other)
    case Right(ts) => SetLattice(ts -- other)
  }

  def --(other: SetLattice[A]): SetLattice[A] = other.s match {
    case Right(os) => this -- os
    case Left(os) => s match {
      case Right(ts) => SetLattice(ts.intersect(os.excluded))    /* ts -- (top except os) == ts/\os */
      case Left(ts) => SetLattice(ts -- os)
    }
  }

  override def toString: String = s match {
    case Left(ts) => "top except " + ts.toString
    case Right(ts) => ts.toString()
  }

  //@TODO Move into pretty printer and also pretty print the elements of ts.
  def prettyString: String = s match {
    case Left(ts) => "top except {" + ts.excluded.mkString(",") + "}"
    case Right(ts) => "{" + ts.mkString(",") + "}"
  }

  //@TODO Code Review suggests conversion to case class, for hashCode and type confusion reasons.
  override def equals(other: Any): Boolean = other match {
    case ls: SetLattice[A] => s match {
      case Left(ts) => ls.s match {
        case Left(os) => ts == os
        case Right(_) => false
      }
      case Right(ts) => ls.s match {
        case Left(_) => false
        case Right(os) => ts == os
      }
    }
    case os: Set[A] => throw new InternalError("DONT DO THIS")
  }

  def toSetLattice[B >: A]: SetLattice[B] = s match {
    case Right(ts) => new SetLattice(Right(ts.toSet))
    case Left(ts) => new SetLattice(Left(new TopSet(ts.excluded.toSet, ts.symbols.toSet)))
  }

  def toSet[B >: A]: Set[B] = s match {
    case Right(ts) => ts.toSet
    case Left(_) => throw new IllegalStateException("SetLattice.top has no set representation")
  }

  /** Set of verbatim occurring symbols in this (possibly top) SetLattice */
  def toSymbolSet[B >: A]: Set[B] = s match {
    case Right(ts) => ts.toSet
    case Left(ts) => ts.symbols.toSet
  }
}

object SetLattice {
  def apply[A](e: A): SetLattice[A] = new SetLattice(Right(Set(e)))
  def apply[A](s: immutable.Set[A]): SetLattice[A] = new SetLattice(Right(s))
  def apply[A](s: immutable.Seq[A]): SetLattice[A] = new SetLattice(Right(s.toSet))
  private def apply[A](s: TopSet[A]): SetLattice[A] = new SetLattice(Left(s))
  def bottom[A] = new SetLattice(Right(Set.empty[A]))
  def top[A](topSymbols: A*): SetLattice[A] = new SetLattice[A](Left(new TopSet(Set.empty, topSymbols.toSet)))
  //@todo careful: this is an overapproximation of V\cup V'
  def topVarsDiffVars[A >: NamedSymbol](topSymbols: A*): SetLattice[A] = new SetLattice[A](Left(new TopSet(Set(DotTerm, DotFormula), topSymbols.toSet)))
}

