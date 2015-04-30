/**
 * Set Lattices.
 * @author smitsch
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
 * @param symbols The specific symbols contained in the set.
 * @tparam A The type of elements.
 */
class TopSet[A](val excluded: immutable.Set[A], val symbols: immutable.Set[A]) {
  /* (top except ts) /\ (top except os) == (top except ts++os) */
  def intersect(other: TopSet[A]): TopSet[A] = new TopSet(excluded ++ other.excluded, symbols.intersect(other.symbols))
  /* this top is a subset of that top if that excluded at most this's excluded */
  def subsetOf(other: TopSet[A]): Boolean = other.excluded.subsetOf(excluded)
  /* top contains everything that's not excluded */
  def contains(e: A): Boolean = !excluded.contains(e)
  /* top contains everything that's imaginable */
  def exists(pred: A => Boolean): Boolean = true
  /* top excludes one element less now */
  def +(e: A): TopSet[A] = new TopSet(excluded - e, symbols + e)
  def ++(other: Set[A]): TopSet[A] = new TopSet(excluded -- other, symbols ++ other)
  def ++(other: GenTraversableOnce[A]): TopSet[A] = new TopSet(excluded -- other, symbols ++ other)
  /* (top except ts) ++ (top except os) == (top except ts/\os) */
  def ++(other: TopSet[A]): TopSet[A] = new TopSet(excluded.intersect(other.excluded), symbols ++ other.symbols)
  /* top now excludes one more element */
  def -(e: A): TopSet[A] = new TopSet(excluded + e, symbols - e)
  def --(other: Set[A]): TopSet[A] = new TopSet(excluded ++ other, symbols -- other)
  def --(other: GenTraversableOnce[A]): TopSet[A] = new TopSet(excluded ++ other, symbols -- other)
  /* (top except ts) -- (top except os) == os -- ts */
  def --(other: TopSet[A]): Set[A] = other.excluded -- excluded

  def map[B](trafo: A => B): TopSet[B] = new TopSet(excluded.map(trafo), symbols.map(trafo))

  override def equals(other: Any): Boolean = other match {
    case os: TopSet[A] => excluded == os.excluded && symbols == os.symbols
    case _ => false
  }
}

object SetLattice {
  def apply[A](e: A): SetLattice[A] = new SetLattice(Right(Set(e)))
  def apply[A](s: Set[A]): SetLattice[A] = new SetLattice(Right(s))
  def apply[A](s: Seq[A]): SetLattice[A] = new SetLattice(Right(s.toSet))
  def bottom[A] = new SetLattice(Right(Set.empty[A]))
  def top[A](topSymbols: A*): SetLattice[A] = new SetLattice[A](Left(new TopSet(Set.empty, topSymbols.toSet)))
  //@todo careful: this is an overapproximation of V\cup V'
  def topVarsDiffVars[A >: NamedSymbol](topSymbols: A*): SetLattice[A] = new SetLattice[A](Left(new TopSet(Set(DotTerm, DotFormula), topSymbols.toSet)))
  def topExceptDotTerm[A >: NamedSymbol](topSymbols: A*): SetLattice[A] = new SetLattice[A](Left(new TopSet(Set(DotTerm), topSymbols.toSet)))
  def topExceptDotFormula[A >: NamedSymbol](topSymbols: A*): SetLattice[A] = new SetLattice[A](Left(new TopSet(Set(DotFormula), topSymbols.toSet)))
}
/**
 * Lattice of sets. Top includes all elements, except the ones listed. Bottom is the empty set.
 * @todo s should be private for abstraction purposes.
 * @param s Elements in the set: Left[A] elements excluded from the set, Right[A] elements included in the set
 * @tparam A Type of elements in the set
 * @todo SetLattice[+A]
 */
class SetLattice[A](@deprecated val s: Either[TopSet[A], immutable.Set[A]]) {
  def isTop = s.isLeft
  def intersect(other: SetLattice[A]): SetLattice[A] = s match {
    case Left(ts) => other.s match {
      case Left(os) => new SetLattice(Left(ts.intersect(os)))
      case Right(os) => SetLattice(os -- ts.excluded)          /* (top except ts) /\ os == os--ts */
    }
    case Right(ts) => other.s match {
      case Left(os) => SetLattice(ts -- os.excluded)           /* ts /\ (top except os) == ts--os */
      case Right(os) => SetLattice(ts.intersect(os))
    }
  }
  def intersect(other: Set[A]): SetLattice[A] = s match {
    case Left(ts) => SetLattice(other -- ts.excluded)
    case Right(ts) => SetLattice(ts.intersect(other))
  }
  def subsetOf(other: SetLattice[A]): Boolean = s match {
    case Left(ts) => other.s match {
      case Left(os) => ts.subsetOf(os)
      case Right(_) => false           /* not a subset of anyhting else */
    }
    case Right(ts) => other.s match {
      case Left(os) => ts.intersect(os.excluded).isEmpty /* this is a subset of that top if that doesn't exclude any of this */
      case Right(os) => ts.subsetOf(os)
    }
  }
  def contains(elem: A): Boolean = s match {
    case Left(ts) => ts.contains(elem)
    case Right(ts) => ts.contains(elem)
  }
  def isEmpty: Boolean = s match {
    case Left(_) => false /* top is never empty, no matter how much it excludes */
    case Right(ts) => ts.isEmpty
  }
  def exists(pred: A => Boolean): Boolean = s match {
    case Left(ts) => ts.exists(pred)
    case Right(ts) => ts.exists(pred)
  }
  def map[B](trafo: A => B): SetLattice[B] = s match {
    case Left(ts) => new SetLattice(Left(ts.map(trafo)))
    case Right(ts) => SetLattice(ts.map(trafo))
  }

  def +(elem: A): SetLattice[A] = s match {
    case Left(ts) => new SetLattice(Left(ts + elem))
    case Right(ts) => SetLattice(ts+elem)
  }
  def -(elem: A): SetLattice[A] = s match {
    case Left(ts) => new SetLattice(Left(ts - elem))
    case Right(ts) => SetLattice(ts-elem)
  }
  /** Set union */
  def ++(other: SetLattice[A]): SetLattice[A] = s match {
    case Left(ts) => other.s match {
      case Left(os) => new SetLattice(Left(ts ++ os))
      case Right(os) => new SetLattice(Left(ts ++ os))
    }
    case Right(ts) => other.s match {
      case Left(os) => new SetLattice(Left(os ++ ts))
      case Right(os) => SetLattice(ts ++ os)
    }
  }
  def ++(other: GenTraversableOnce[A]): SetLattice[A] = s match {
    case Left(ts) => new SetLattice(Left(ts ++ other))
    case Right(ts) => SetLattice(ts ++ other)
  }
  /** Set subtraction */
  def --(other: SetLattice[A]): SetLattice[A] = s match {
    case Left(ts) => other.s match {
      case Left(os) => SetLattice(os -- ts)
      case Right(os) => new SetLattice(Left(ts -- os))
    }
    case Right(ts) => other.s match {
      case Left(os) => SetLattice(ts.intersect(os.excluded))    /* ts -- (top except os) == ts/\os */
      case Right(os) => SetLattice(ts -- os)
    }
  }
  def --(other: GenTraversableOnce[A]): SetLattice[A] = s match {
    case Left(ts) => new SetLattice(Left(ts -- other))
    case Right(ts) => SetLattice(ts -- other)
  }
  override def toString = s match {
    case Left(ts) => "top except " + ts.toString
    case Right(ts) => ts.toString()
  }
  //@TODO Move into pretty printer and also pretty print the elements of ts.
  def prettyString = s match {
    case Left(ts) => "top except {" + ts.excluded.mkString(",") + "}"
    case Right(ts) => "{" + ts.mkString(",") + "}"
  }
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
    case os: Set[A] => s match {
      case Left(_) => false
      case Right(ts) => ts == os
    }
  }

  def toSetLattice[B >: A]: SetLattice[B] = s match {
    case Right(ts) => new SetLattice(Right(ts.toSet))
    case Left(ts) => new SetLattice(Left(new TopSet(ts.excluded.toSet, ts.symbols.toSet)))
  }

  def toSet[B >: A]: Set[B] = s match {
    case Right(ts) => ts.toSet
    case Left(_) => throw new IllegalStateException("SetLattice.top has no set representation")
  }

  def toSymbolSet[B >: A]: Set[B] = s match {
    case Right(ts) => ts.toSet
    case Left(ts) => ts.symbols.toSet
  }
}

