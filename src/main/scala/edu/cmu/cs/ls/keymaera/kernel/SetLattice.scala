/**
 * Set Lattices.
 * @author smitsch
 */
package edu.cmu.cs.ls.keymaera.kernel


//  type SetLattice[A] = Set[A]
//  private def topExceptDotFormula[A]: Set[A] = ???
//  private def topExceptDotTerm[A]: Set[A] = ???

//object SetLattice {
//  def apply[A](e: A): Set[A] = Set(e)
//  def bottom[A]: Set[A] = Set()
//}

object SetLattice {
  def apply[A](e: A): SetLattice[A] = new SetLattice(Right(Set(e)))
  def apply[A](s: Set[A]): SetLattice[A] = new SetLattice(Right(s))
  def apply[A](s: Seq[A]): SetLattice[A] = new SetLattice(Right(s.toSet))
  def bottom[A] = new SetLattice(Right(Set.empty[A]))
  def top[A]: SetLattice[A] = new SetLattice[A](Left(Set.empty))
  def topExceptDotTerm[A >: NamedSymbol]: SetLattice[A] = new SetLattice[A](Left(Set(DotTerm)))
  def topExceptDotFormula[A >: NamedSymbol]: SetLattice[A] = new SetLattice[A](Left(Set(DotFormula)))
}
/**
 * Lattice of sets. Top includes all elements, except the ones listed. Bottom is the empty set.
 * @todo s should be private for abstraction purposes.
 * @param s Elements in the set: Left[A] elements excluded from the set, Right[A] elements included in the set
 * @tparam A Type of elements in the set
 */
class SetLattice[A](@deprecated val s: Either[Set[A], Set[A]]) {
  def isTop = s.isLeft
  def intersect(other: SetLattice[A]): SetLattice[A] = s match {
    case Left(ts) => other.s match {
      case Left(os) => new SetLattice(Left(ts ++ os)) /* (top except ts) /\ (top except os) == (top except ts++os) */
      case Right(os) => SetLattice(os -- ts)          /* (top except ts) /\ os == os--ts */
    }
    case Right(ts) => other.s match {
      case Left(os) => SetLattice(ts -- os)           /* ts /\ (top except os) == ts--os */
      case Right(os) => SetLattice(ts.intersect(os))
    }
  }
  def intersect(other: Set[A]): SetLattice[A] = s match {
    case Left(ts) => SetLattice(other -- ts)
    case Right(ts) => SetLattice(ts.intersect(other))
  }
  def subsetOf(other: SetLattice[A]): Boolean = s match {
    case Left(ts) => other.s match {
      case Left(os) => os.subsetOf(ts) /* this top is a subset of that top if that excluded at most this's excluded */
      case Right(_) => false           /* not a subset of anyhting else */
    }
    case Right(ts) => other.s match {
      case Left(os) => ts.intersect(os).isEmpty /* this is a subset of that top if that doesn't exclude any of this */
      case Right(os) => ts.subsetOf(os)
    }
  }
  def contains(elem: A): Boolean = s match {
    case Left(ts) => !ts.contains(elem) /* top contains everything that's not excluded */
    case Right(ts) => ts.contains(elem)
  }
  def isEmpty: Boolean = s match {
    case Left(_) => false /* top is never empty, no matter how much it excludes */
    case Right(ts) => ts.isEmpty
  }
  def exists(pred: A => Boolean): Boolean = s match {
    case Left(_) => true /* top contains everything that's imaginable */
    case Right(ts) => ts.exists(pred)
  }
  def map[B](trafo: A => B): SetLattice[B] = s match {
    case Left(ts) => new SetLattice(Left(ts.map(trafo)))
    case Right(ts) => SetLattice(ts.map(trafo))
  }

  def +(elem: A): SetLattice[A] = s match {
    case Left(ts) => new SetLattice(Left(ts - elem)) /* top excludes one element less now */
    case Right(ts) => SetLattice(ts+elem)
  }
  def -(elem: A): SetLattice[A] = s match {
    case Left(ts) => new SetLattice(Left(ts + elem)) /* top now excludes one more element */
    case Right(ts) => SetLattice(ts-elem)
  }
  /** Set union */
  def ++(other: SetLattice[A]): SetLattice[A] = s match {
    case Left(ts) => other.s match {
      case Left(os) => new SetLattice(Left(ts.intersect(os))) /* (top except ts) ++ (top except os) == (top except ts/\os) */
      case Right(os) => new SetLattice(Left(ts -- os))        /* (top except ts) ++ os == (top except ts--os) */
    }
    case Right(ts) => other.s match {
      case Left(os) => new SetLattice(Left(os -- ts))         /* ts ++ (top except os) == top except os--ts */
      case Right(os) => SetLattice(ts ++ os)
    }
  }
  def ++(other: GenTraversableOnce[A]): SetLattice[A] = s match {
    case Left(ts) => new SetLattice(Left(ts -- other))
    case Right(ts) => SetLattice(ts ++ other)
  }
  /** Set subtraction */
  def --(other: SetLattice[A]): SetLattice[A] = s match {
    case Left(ts) => other.s match {
      case Left(os) => SetLattice(os -- ts)            /* (top except ts) -- (top except os) == os -- ts */
      case Right(os) => new SetLattice(Left(ts ++ os)) /* (top except ts) -- os == (top except ts++os) */
    }
    case Right(ts) => other.s match {
      case Left(os) => SetLattice(ts.intersect(os))    /* ts -- (top except os) == ts/\os */
      case Right(os) => SetLattice(ts -- os)
    }
  }
  def --(other: GenTraversableOnce[A]): SetLattice[A] = s match {
    case Left(ts) => new SetLattice(Left(ts ++ other)) /* (top except ts) -- other == (top except ts++other) */
    case Right(ts) => SetLattice(ts -- other)
  }
  override def toString = s match {
    case Left(ts) => "top except " + ts.toString()
    case Right(ts) => ts.toString()
  }
  //@TODO Move into pretty printer and also pretty print the elements of ts.
  def prettyString = s match {
    case Left(ts) => "top except {" + ts.mkString(",") + "}"
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

  def toSet: Set[A] = s match {
    case Right(ts) => ts
    case Left(_) => throw new IllegalStateException("SetLattice.top has no set representation")
  }
}

