/**
 * The static semantics of differential dynamic logic.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaera.core

// favoring immutable Seqs for soundness

import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.Set

import scala.annotation.{unspecialized, elidable}
import scala.annotation.elidable._

import edu.cmu.cs.ls.keymaera.core.Number.NumberObj

import scala.collection.GenTraversableOnce

/**
 * The static semantics of differential dynamic logic.
 * @author aplatzer
 * @author smitsch
 */
object StaticSemantics {
  
  /**
   * Structure recording which names are free or bound
   * in a formula.
   * @param fv Free names (maybe read)
   * @param bv Bound names (maybe written)
   */
  sealed case class VCF(fv: SetLattice[NamedSymbol],
                        bv: SetLattice[NamedSymbol])

  /**
   * Structure recording which names are free, bound, or must-bound
   * in a program.
   * @param fv Free names (maybe read)
   * @param bv Bound names (maybe written)
   * @param mbv Must-bound names (certainly written).
   */
  sealed case class VCP(fv: SetLattice[NamedSymbol],
                        bv: SetLattice[NamedSymbol],
                        mbv: SetLattice[NamedSymbol])
  
  // variables
  
  /**
   * Compute the static semantics of term t, i.e., the set of its free variables.
   */
  def apply(t: Term): SetLattice[NamedSymbol] = freeVars(t)

  /**
   * Compute the static semantics of formula f, i.e., its set of free and bound variables.
   */
  def apply(f: Formula): VCF = fmlVars(f)

  /**
   * Compute the static semantics of program a, i.e., its set of free and bound and must-bound variables.
   */
  def apply(a: Program): VCP = progVars(a)


  /**
   * The set FV(e) of free variables of expression e.
   */
  def freeVars(e: Expr): SetLattice[NamedSymbol] = e match {
    case t: Term => freeVars(t)
    case f: Formula => freeVars(f)
    case a: Program => freeVars(a)
  }

  /**
   * The set FV(t) of free variables of term t.
   */
  def freeVars(t: Term): SetLattice[NamedSymbol] = {t match {
    // base cases
    case x: Variable => SetLattice(x)
    case xp: DifferentialSymbol => SetLattice(xp)
    case CDot => assert(!CDot.isInstanceOf[Variable], "CDot is no variable"); SetLattice.bottom
    // homomorphic cases
    case Apply(f, arg) => freeVars(arg)
    case Neg(s, l) => freeVars(l)
    case Add(s, l, r) => freeVars(l) ++ freeVars(r)
    case Subtract(s, l, r) => freeVars(l) ++ freeVars(r)
    case Multiply(s, l, r) => freeVars(l) ++ freeVars(r)
    case Divide(s, l, r) => freeVars(l) ++ freeVars(r)
    case Exp(s, l, r) => freeVars(l) ++ freeVars(r)
    case Pair(dom, l, r) => freeVars(l) ++ freeVars(r)
    // special cases
    case Derivative(s, x:NamedSymbol) => SetLattice(DifferentialSymbol(x)) //@TODO This case is weird
    case Derivative(s, e) => val fv = freeVars(e); fv ++ fv.map[NamedSymbol](x=>DifferentialSymbol(x))
    case _: NumberObj | Nothing | Anything => SetLattice.bottom
  }}/*@TODO ensuring (r => r != SetLattice.top,
    "terms cannot have top as free variables, since they cannot mention all free variables but only some")*/
  
  /**
   * The set FV(f) of free variables of formula f.
   */
  def freeVars(f: Formula): SetLattice[NamedSymbol] = StaticSemantics(f).fv

  /**
   * The set FV(a) of free variables of program a.
   */
  def freeVars(a: Program): SetLattice[NamedSymbol] = StaticSemantics(a).fv

  /**
   * The set BV(f) of bound variables of formula f.
   */
  def boundVars(f: Formula): SetLattice[NamedSymbol] = StaticSemantics(f).bv

  /**
   * The set BV(a) of bound variables of program a.
   */
  def boundVars(a: Program): SetLattice[NamedSymbol] = StaticSemantics(a).bv

  private def fmlVars(f: Formula): VCF = f match {
    // base cases
    case Equals(d, l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = SetLattice.bottom)
    case NotEquals(d, l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = SetLattice.bottom)
    case GreaterEqual(d, l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = SetLattice.bottom)
    case GreaterThan(d, l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = SetLattice.bottom)
    case LessEqual(d, l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = SetLattice.bottom)
    case LessThan(d, l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = SetLattice.bottom)
    case ApplyPredicate(p, arg) => VCF(fv = freeVars(arg), bv = SetLattice.bottom)
    case ApplyPredicational(p, arg) => VCF(fv = SetLattice.topExceptCDotFormula, bv = SetLattice.bottom)
    case CDotFormula => VCF(fv = SetLattice.topExceptCDotFormula, bv = SetLattice.bottom)

    // homomorphic cases
    case Not(g) => val vg = fmlVars(g); VCF(fv = vg.fv, bv = vg.bv)
    case And(l, r) => val vl = fmlVars(l); val vr = fmlVars(r); VCF(fv = vl.fv ++ vr.fv, bv = vl.bv ++ vr.bv)
    case Or(l, r) => val vl = fmlVars(l); val vr = fmlVars(r); VCF(fv = vl.fv ++ vr.fv, bv = vl.bv ++ vr.bv)
    case Imply(l, r) => val vl = fmlVars(l); val vr = fmlVars(r); VCF(fv = vl.fv ++ vr.fv, bv = vl.bv ++ vr.bv)
    case Equiv(l, r) => val vl = fmlVars(l); val vr = fmlVars(r); VCF(fv = vl.fv ++ vr.fv, bv = vl.bv ++ vr.bv)

    // quantifier binding cases omit bound vars from fv and add bound variables to bf
    case Forall(vars, g) => val vg = fmlVars(g); VCF(fv = vg.fv -- vars, bv = vg.bv ++ vars)
    case Exists(vars, g) => val vg = fmlVars(g); VCF(fv = vg.fv -- vars, bv = vg.bv ++ vars)

    // modality bounding cases omit must-bound vars from fv and add (may-)bound vars to bv
    case BoxModality(p, g) => val vp = apply(p); val vg = fmlVars(g);
      VCF(fv = vp.fv ++ (vg.fv -- vp.mbv), bv = vp.bv ++ vg.bv)
    case DiamondModality(p, g) => val vp = apply(p); val vg = fmlVars(g);
      VCF(fv = vp.fv ++ (vg.fv -- vp.mbv), bv = vp.bv ++ vg.bv)

    // special cases
    // TODO formuladerivative not mentioned in Definition 7 and 8
    case FormulaDerivative(df) => val vdf = fmlVars(df); VCF(fv = vdf.fv ++ vdf.fv.map[NamedSymbol](x=>DifferentialSymbol(x)), bv = vdf.bv) //@todo eisegesis
    case True | False => VCF(fv = SetLattice.bottom, bv = SetLattice.bottom)
  }

  private def progVars(p: Program): VCP = { p match {
    // base cases
    case _: ProgramConstant => VCP(fv = SetLattice.topExceptCDot, bv = SetLattice.topExceptCDot, mbv = SetLattice.bottom) //@TODO this includes x,x' for all x?
    case _: DifferentialProgramConstant => VCP(fv = SetLattice.topExceptCDot, bv = SetLattice.topExceptCDot, mbv = SetLattice.bottom)
    case Assign(x: Variable, e) => VCP(fv = apply(e), bv = SetLattice(x), mbv = SetLattice(x))
    case Assign(Derivative(_, x : NamedSymbol), e) => VCP(fv = apply(e), bv = SetLattice(DifferentialSymbol(x)), mbv = SetLattice(DifferentialSymbol(x)))
    case Assign(x : DifferentialSymbol, e) => {throw new Exception("wasn't expecting to get here."); VCP(fv = freeVars(e), bv = SetLattice(x), mbv = SetLattice(x))}
    case AtomicODE(Derivative(_, x: Variable), e) =>
      VCP(fv = SetLattice[NamedSymbol](x) ++ apply(e), bv = SetLattice[NamedSymbol](x) ++ SetLattice[NamedSymbol](DifferentialSymbol(x)), mbv = SetLattice[NamedSymbol](x) ++ SetLattice[NamedSymbol](DifferentialSymbol(x)))
    case Test(f) => VCP(fv = apply(f).fv, bv = SetLattice.bottom, mbv = SetLattice.bottom)
    case IfThen(cond, thenT) => val vThen = progVars(thenT); val vCond = VCP(fv = apply(cond).fv, bv = SetLattice.bottom, mbv = SetLattice.bottom);
                                VCP(fv = vCond.fv ++ vThen.fv, bv = vCond.bv ++ vThen.bv, mbv = vCond.mbv ++ vThen.mbv) //@todo eisegesis
    // combinator cases
    case Choice(a, b) => val va = progVars(a); val vb = progVars(b)
      VCP(fv = va.fv ++ vb.fv, bv = va.bv ++ vb.bv, mbv = va.mbv.intersect(vb.mbv))
    case Sequence(a, b) => val va = progVars(a); val vb = progVars(b)
      VCP(fv = va.fv ++ (vb.fv -- va.mbv), bv = va.bv ++ vb.bv, mbv = va.mbv ++ vb.mbv)
    case Loop(a) => val va = progVars(a); VCP(fv = va.fv, bv = va.bv, mbv = SetLattice.bottom)

    // special cases //@TODO check all special cases
    //@NOTE x:=* not mentioned in Definition 9
    case NDetAssign(x: Variable) => VCP(fv = SetLattice.bottom, bv = SetLattice(x), mbv = SetLattice(x))
    // TODO system of ODE cases not mentioned in Definition 9
    case ODESystem(v, a, h) => val va = progVars(a); VCP(fv = (va.fv ++ apply(h).fv) -- v, bv = va.bv ++ v, mbv = va.mbv ++ v)
    case ODEProduct(a, b) => val va = progVars(a); val vb = progVars(b)
      VCP(fv = va.fv ++ vb.fv, bv = va.bv ++ vb.bv, mbv = va.mbv ++ vb.mbv)
    case IncompleteSystem(a) => progVars(a) //@todo eisegesis
    case CheckedContEvolveFragment(a) => progVars(a) //@todo eisegesis
    case _: EmptyODE => VCP(fv = SetLattice.bottom, bv = SetLattice.bottom, mbv = SetLattice.bottom)
  }} ensuring(r => { val VCP(_, bv, mbv) = r; mbv.subsetOf(bv) }, s"Result MBV($p) must be a subset of BV($p)")

  // signature of function, predicate, atomic program symbols

  /**
   * The signature of expression e.
   */
  def signature(e: Expr): Set[NamedSymbol] = e match {
    case t: Term => signature(t)
    case f: Formula => signature(f)
    case a: Program => signature(a)
  }

  /**
   * The signature of a term, i.e., set of function symbols occurring in it.
   * Disregarding number literals.
   * @TODO Change return type to Set[Function]
   */
  def signature(t: Term): Set[NamedSymbol] = t match {
    // base cases
    case Apply(f, arg) => Set(f) ++ signature(arg)
    case x: Variable => Set.empty
    case CDot => Set(CDot)
    case nd: DifferentialSymbol => Set.empty
    // homomorphic cases
    case Neg(s, e) => signature(e)
    case Add(s, l, r) => signature(l) ++ signature(r)
    case Subtract(s, l, r) => signature(l) ++ signature(r)
    case Multiply(s, l, r) => signature(l) ++ signature(r)
    case Divide(s, l, r) => signature(l) ++ signature(r)
    case Exp(s, l, r) => signature(l) ++ signature(r)
    case Pair(dom, l, r) => signature(l) ++ signature(r)
    case Derivative(s, e) => signature(e)
    // special
    case _: NumberObj | Nothing | Anything => Set.empty
  }
  //ensuring (r => r.forall(f => isInstanceOf[Function](f)), "signature of term " + t + " can only be functions")

  /**
   * The signature of a formula, i.e., set of function, predicate, and atomic program 
   * symbols occurring in it.
   */
  def signature(f: Formula): Set[NamedSymbol] = f match {
    // base cases
    case ApplyPredicate(p, arg) => Set(p) ++ signature(arg)
    case ApplyPredicational(p, arg) => Set(p) ++ signature(arg)
    case CDotFormula => Set(CDotFormula)
    case True | False => Set.empty
    // pseudo-homomorphic cases
    case Equals(d, l, r) => signature(l) ++ signature(r)
    case NotEquals(d, l, r) => signature(l) ++ signature(r)
    case GreaterEqual(d, l, r) => signature(l) ++ signature(r)
    case GreaterThan(d, l, r) => signature(l) ++ signature(r)
    case LessEqual(d, l, r) => signature(l) ++ signature(r)
    case LessThan(d, l, r) => signature(l) ++ signature(r)

    // homomorphic cases
    case Not(g) => signature(g)
    case And(l, r) => signature(l) ++ signature(r)
    case Or(l, r) => signature(l) ++ signature(r)
    case Imply(l, r) => signature(l) ++ signature(r)
    case Equiv(l, r) => signature(l) ++ signature(r)
    case FormulaDerivative(df) => signature(df)

    case Forall(vars, g) => signature(g)
    case Exists(vars, g) => signature(g)

    case BoxModality(p, g) => signature(p) ++ signature(g)
    case DiamondModality(p, g) => signature(p) ++ signature(g)

  }

  /**
   * The signature of a program, i.e., set of function, predicate, and atomic program 
   * symbols occurring in it.
   */
  def signature(p: Program): Set[NamedSymbol] = p match {
    // base cases
    case ap: ProgramConstant => Set(ap)
    case ap: DifferentialProgramConstant => Set(ap)
    case Assign(x: Variable, e) => signature(e)
    case Assign(x : DifferentialSymbol, e) => signature(e)
    case Assign(Derivative(_, x : NamedSymbol), e) => signature(e)
    case NDetAssign(x: Variable) => Set.empty
    case Test(f) => signature(f)
    case IfThen(cond, thenT) => signature(thenT) ++ signature(cond)
    case AtomicODE(Derivative(_, x: Variable), e) => signature(e)
    case ODESystem(vars, a, h) => signature(a) ++ signature(h)
    case ODEProduct(a, b) => signature(a) ++ signature(b)
    case IncompleteSystem(a) => signature(a)
    case CheckedContEvolveFragment(a) => signature(a)
    case _: EmptyODE => Set()
    // homomorphic cases
    case Choice(a, b) => signature(a) ++ signature(b)
    case Sequence(a, b) => signature(a) ++ signature(b)
    case Loop(a) => signature(a)
  }
  
  /**
   * Any symbols in expression e.
   */
  def symbols(e: Expr): Set[NamedSymbol] = e match {
    case t: Term => symbols(t)
    case f: Formula => symbols(f)
    case a: Program => symbols(a)
  }

  /**
   * Any symbol occuring in term, whether variable or function
   */
  def symbols(t : Term): Set[NamedSymbol] = signature(t) ++ freeVars(t).toSet

  /**
   * Any symbol occuring in formula, whether free or bound variable or function or predicate or program constant
   */
  def symbols(f : Formula): Set[NamedSymbol] = {val stat = apply(f); signature(f) ++ stat.fv.toSet ++ stat.bv.toSet}

  /**
   * Any symbol occuring in program, whether free or bound variable or function or predicate or program constant
   */
  def symbols(p : Program): Set[NamedSymbol] = {val stat = apply(p); signature(p) ++ stat.fv.toSet ++ stat.bv.toSet}
}


object SetLattice {
  def apply[A](e: A): SetLattice[A] = new SetLattice(Right(Set(e)))
  def apply[A](s: Set[A]): SetLattice[A] = new SetLattice(Right(s))
  def apply[A](s: Seq[A]): SetLattice[A] = new SetLattice(Right(s.toSet))
  def bottom[A] = new SetLattice(Right(Set.empty[A]))
  def top[A]: SetLattice[A] = new SetLattice[A](Left(Set.empty))
  def topExceptCDot[A >: NamedSymbol]: SetLattice[A] = new SetLattice[A](Left(Set(CDot)))
  def topExceptCDotFormula[A >: NamedSymbol]: SetLattice[A] = new SetLattice[A](Left(Set(CDotFormula)))
}
/**
 * Lattice of sets. Top includes all elements, except the ones listed. Bottom is the empty set.
 * @TODO s should be private for abstraction purposes.
 * @param s Elements in the set: Left[A] elements excluded from the set, Right[A] elements included in the set
 * @tparam A Type of elements in the set
 */
class SetLattice[A](val s: Either[Set[A], Set[A]]) {
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

