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
  
  /**
   * Compute the static semantics of term t, i.e., the set of its free variables.
   */
  def apply(t: Term): SetLattice[NamedSymbol] = freeVars(t)

  private def freeVars(t: Term): SetLattice[NamedSymbol] = t match {
    // base cases
    case x: Variable => SetLattice(x)
    case CDot => SetLattice(CDot)
    case NamedDerivative(x : NamedSymbol) => SetLattice(NamedDerivative(x))
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
    case Derivative(s, x:NamedSymbol) => SetLattice(NamedDerivative(x)) //@TODO This case is weird
    case Derivative(s, e) => val fv = freeVars(e); fv ++ fv.map(x=>NamedDerivative(x))
    case True | False | _: NumberObj | Nothing | Anything => SetLattice.bottom
  }

  /**
   * Compute the static semantics of formula f, i.e., its set of free and bound variables.
   */
  def apply(f: Formula): VCF = fmlVars(f)

  private def fmlVars(f: Formula): VCF = f match {
    // base cases
    case Equals(d, l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = SetLattice.bottom)
    case NotEquals(d, l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = SetLattice.bottom)
    case GreaterEqual(d, l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = SetLattice.bottom)
    case GreaterThan(d, l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = SetLattice.bottom)
    case LessEqual(d, l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = SetLattice.bottom)
    case LessThan(d, l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = SetLattice.bottom)
    case ApplyPredicate(p, arg) => VCF(fv = freeVars(arg), bv = SetLattice.bottom)

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
    case FormulaDerivative(df) => val vdf = fmlVars(df); VCF(fv = vdf.fv ++ vdf.fv.map(x=>NamedDerivative(x)), bv = vdf.bv) //@todo eisegesis
    case True | False => VCF(fv = SetLattice.bottom, bv = SetLattice.bottom)
  }

  /**
   * Compute the static semantics of program a, i.e., its set of free and bound and must-bound variables.
   */
  def apply(a: Program): VCP = progVars(a)

  private def progVars(p: Program): VCP = { p match {
    // base cases
    case _: ProgramConstant => VCP(fv = SetLattice.top, bv = SetLattice.top, mbv = SetLattice.bottom) //@TODO this includes x,x' for all x?
    case _: ContEvolveProgramConstant => VCP(fv = SetLattice.top, bv = SetLattice.top, mbv = SetLattice.bottom)
    case Assign(x: Variable, e) => VCP(fv = apply(e), bv = SetLattice(x), mbv = SetLattice(x))
    case Assign(Derivative(_, x : NamedSymbol), e) => VCP(fv = apply(e), bv = SetLattice(NamedDerivative(x)), mbv = SetLattice(NamedDerivative(x)))
    case Assign(x : NamedDerivative, e) => {throw new Exception("wasn't expecting to get here."); VCP(fv = freeVars(e), bv = SetLattice(x), mbv = SetLattice(x))}
    case Test(f) => VCP(fv = apply(f).fv, bv = SetLattice.bottom, mbv = SetLattice.bottom)
    // combinator cases
    case Choice(a, b) => val va = progVars(a); val vb = progVars(b)
      VCP(fv = va.fv ++ vb.fv, bv = va.bv ++ vb.bv, mbv = va.mbv.intersect(vb.mbv))
    case Sequence(a, b) => val va = progVars(a); val vb = progVars(b)
      VCP(fv = va.fv ++ (vb.fv -- va.mbv), bv = va.bv ++ vb.bv, mbv = va.mbv ++ vb.mbv)
    case Loop(a) => val va = progVars(a); VCP(fv = va.fv, bv = va.bv, mbv = SetLattice.bottom)

    // special cases //@TODO check all special cases
    //@NOTE x:=* not mentioned in Definition 9
    case NDetAssign(x: Variable) => VCP(fv = SetLattice.bottom, bv = SetLattice(x), mbv = SetLattice(x))
    case NFContEvolve(vars, Derivative(_, x: Variable), e, h) =>
      VCP(fv = SetLattice[NamedSymbol](x) ++ apply(e) ++ apply(h).fv, bv = SetLattice[NamedSymbol](x) ++ SetLattice[NamedSymbol](NamedDerivative(x)), mbv = SetLattice[NamedSymbol](x) ++ SetLattice[NamedSymbol](NamedDerivative(x)))
    // TODO system of ODE cases not mentioned in Definition 9
    case ContEvolveProduct(a, b) => val va = progVars(a); val vb = progVars(b)
      VCP(fv = va.fv ++ vb.fv, bv = va.bv ++ vb.bv, mbv = va.mbv ++ vb.mbv) //@todo eisegesis
    case IncompleteSystem(a) => progVars(a) //@todo eisegesis
    case CheckedContEvolveFragment(a) => progVars(a) //@todo eisegesis
    case _: EmptyContEvolveProgram => VCP(fv = SetLattice.bottom, bv = SetLattice.bottom, mbv = SetLattice.bottom) //@todo eisegesis
  }} ensuring(r => { val VCP(_, bv, mbv) = r; mbv.subsetOf(bv) }, s"Result MBV($p) must be a subset of BV($p)")

}

