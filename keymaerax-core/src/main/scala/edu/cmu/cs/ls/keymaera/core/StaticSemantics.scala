/**
 * The static semantics of differential dynamic logic.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaera.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.SortedSet
import scala.collection.immutable.Set


import scala.annotation.elidable

/**
 * The static semantics of differential dynamic logic.
 * @author aplatzer
 * @author smitsch
 */
object StaticSemantics {

  import SetLattice.topVarsDiffVars
  import SetLattice.bottom

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
  def freeVars(e: Expression): SetLattice[NamedSymbol] = e match {
    case t: Term => freeVars(t)
    case f: Formula => freeVars(f)
    case a: Program => freeVars(a)
  }

  /**
   * The set FV(t) of free variables of term t.
   */
  def freeVars(t: Term): SetLattice[NamedSymbol] = {
    t match {
      // base cases
      case x: Variable => SetLattice(x)
      case xp: DifferentialSymbol => SetLattice(xp)
      case _: Number => bottom
      case DotTerm => assert(!DotTerm.isInstanceOf[Variable], "DotTerm is no variable"); bottom
      // homomorphic cases
      case FuncOf(f, arg) => freeVars(arg)
      case Neg(e) => freeVars(e)
      case Plus(l, r) => freeVars(l) ++ freeVars(r)
      case Minus(l, r) => freeVars(l) ++ freeVars(r)
      case Times(l, r) => freeVars(l) ++ freeVars(r)
      case Divide(l, r) => freeVars(l) ++ freeVars(r)
      case Power(l, r) => freeVars(l) ++ freeVars(r)
      // special cases
      case Differential(e) => val fv = freeVars(e); fv ++ differentialSymbols(fv)
      // unofficial
      case Pair(l, r) => freeVars(l) ++ freeVars(r)
      case Nothing | Anything => bottom
    }
  } /*ensuring (r => true /*r != SetLattice.top*/,
    "terms cannot have top as free variables, since they cannot mention all free variables but only some")*/

  /**
   * Add ' to a set, i.e. turn all elements x in the lattice into x'
   * @return The set of all x' for which x is in s.
   */
  private[core] def differentialSymbols(s: SetLattice[NamedSymbol]) : SetLattice[NamedSymbol] =
    s.map[NamedSymbol](v => v match {
    case x: Variable => DifferentialSymbol(x)
    case _ => throw new IllegalArgumentException("Unsupported symbol has no differential " + v + " of type " + v.getClass)
  })

  /**
   * The set FV(f) of free variables of formula f.
   */
  def freeVars(f: Formula): SetLattice[NamedSymbol] = StaticSemantics(f).fv

  /**
   * The set FV(a) of free variables of program a.
   */
  def freeVars(a: Program): SetLattice[NamedSymbol] = StaticSemantics(a).fv

  /**
   * The set FV(a) of free variables of a sequent.
   */
  def freeVars(s: Sequent): SetLattice[NamedSymbol] =
    s.ante.foldLeft(bottom[NamedSymbol])((a,b)=>a ++ freeVars(b)) ++
      s.succ.foldLeft(bottom[NamedSymbol])((a,b)=>a ++ freeVars(b))

  /**
   * The set BV(f) of bound variables of formula f.
   */
  def boundVars(f: Formula): SetLattice[NamedSymbol] = StaticSemantics(f).bv

  /**
   * The set BV(a) of bound variables of program a.
   */
  def boundVars(a: Program): SetLattice[NamedSymbol] = StaticSemantics(a).bv

  /**
   * The set BV(a) of bound variables of a sequent.
   */
  def boundVars(s: Sequent): SetLattice[NamedSymbol] =
    s.ante.foldLeft(bottom[NamedSymbol])((a,b)=>a ++ boundVars(b)) ++
      s.succ.foldLeft(bottom[NamedSymbol])((a,b)=>a ++ boundVars(b))

  private def fmlVars(f: Formula): VCF = f match {
    // base cases
    case Equal(l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
    case NotEqual(l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)

    case GreaterEqual(l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
    case Greater(l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
    case LessEqual(l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
    case Less(l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)

    case PredOf(p, arg) => VCF(fv = freeVars(arg), bv = bottom)
    case DotFormula => VCF(fv = topVarsDiffVars(), bv = bottom)
    case PredicationalOf(p, arg) => VCF(fv = topVarsDiffVars(), bv = bottom) //@todo eisegesis bv=topVarsDiffVars?

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
    case Box(p, g) => val vp = apply(p);
      val vg = fmlVars(g);
      VCF(fv = vp.fv ++ (vg.fv -- vp.mbv), bv = vp.bv ++ vg.bv)
    case Diamond(p, g) => val vp = apply(p);
      val vg = fmlVars(g);
      VCF(fv = vp.fv ++ (vg.fv -- vp.mbv), bv = vp.bv ++ vg.bv)

    // special cases
    // TODO DifferentialFormula not mentioned in Definition 7 and 8, analogue to Differential
    case DifferentialFormula(df) => val vdf = fmlVars(df); VCF(fv = vdf.fv ++ differentialSymbols(vdf.fv), bv = vdf.bv) //@todo eisegesis
    case True | False => VCF(fv = bottom, bv = bottom)
  }

  private def progVars(p: Program): VCP = {
    p match {
      // base cases
      case pc: ProgramConst => VCP(fv = topVarsDiffVars(pc), bv = topVarsDiffVars(pc), mbv = bottom)
      case dpc: DifferentialProgramConst => VCP(fv = topVarsDiffVars(dpc), bv = topVarsDiffVars(dpc), mbv = bottom)
      case Assign(x: Variable, e) => VCP(fv = freeVars(e), bv = SetLattice(x), mbv = SetLattice(x))
      case DiffAssign(xp: DifferentialSymbol, e) => VCP(fv = freeVars(e), bv = SetLattice(xp), mbv = SetLattice(xp))
      case Test(f) => VCP(fv = apply(f).fv, bv = bottom, mbv = bottom)
      case AtomicODE(xp@DifferentialSymbol(x: Variable), e) =>
        VCP(fv = SetLattice[NamedSymbol](x) ++ freeVars(e), bv = SetLattice[NamedSymbol](x) ++ SetLattice[NamedSymbol](xp), mbv = SetLattice[NamedSymbol](x) ++ SetLattice[NamedSymbol](xp))
      // combinator cases
      case Choice(a, b) => val va = progVars(a);
        val vb = progVars(b)
        VCP(fv = va.fv ++ vb.fv, bv = va.bv ++ vb.bv, mbv = va.mbv.intersect(vb.mbv))
      case Compose(a, b) => val va = progVars(a);
        val vb = progVars(b)
        VCP(fv = va.fv ++ (vb.fv -- va.mbv), bv = va.bv ++ vb.bv, mbv = va.mbv ++ vb.mbv)
      case Loop(a) => val va = progVars(a); VCP(fv = va.fv, bv = va.bv, mbv = bottom)

      // special cases //@TODO check all special cases
      //@NOTE x:=* not mentioned in Definition 9
      case AssignAny(x: Variable) => VCP(fv = bottom, bv = SetLattice(x), mbv = SetLattice(x))
      // TODO system of ODE cases not mentioned in Definition 9
      case ODESystem(a, h) => val v = bottom[NamedSymbol]; val va = progVars(a); VCP(fv = (va.fv ++ apply(h).fv) -- v, bv = va.bv ++ v, mbv = va.mbv ++ v)
      case DifferentialProduct(a, b) => val va = progVars(a);
        val vb = progVars(b)
        VCP(fv = va.fv ++ vb.fv, bv = va.bv ++ vb.bv, mbv = va.mbv ++ vb.mbv)
    }
  } ensuring(r => {
    val VCP(_, bv, mbv) = r; mbv.subsetOf(bv)
  }, "Result MBV(" + p + ") must be a subset of BV(" + p + ")")

  // signature of function, predicate, atomic program symbols

  /**
   * The signature of expression e.
   * @todo change return types or at least implementation types to SortedSet for order stability?
   */
  def signature(e: Expression): Set[NamedSymbol] = e match {
    case t: Term => signature(t)
    case f: Formula => signature(f)
    case a: Program => signature(a)
  }

  /**
   * The signature of a term, i.e., set of function symbols occurring in it.
   * Disregarding number literals.
   * @todo Change return type to Set[Function]?
   */
  def signature(t: Term): Set[NamedSymbol] = t match {
    // base cases
    case _: Variable => Set.empty
    case _: DifferentialSymbol => Set.empty
    case _: Number => Set.empty
    case DotTerm => Set(DotTerm)
    case FuncOf(f, arg) => Set(f) ++ signature(arg)
    // homomorphic cases
    case Neg(e) => signature(e)
    case Plus(l, r) => signature(l) ++ signature(r)
    case Minus(l, r) => signature(l) ++ signature(r)
    case Times(l, r) => signature(l) ++ signature(r)
    case Divide(l, r) => signature(l) ++ signature(r)
    case Power(l, r) => signature(l) ++ signature(r)
    case Differential(e) => signature(e)
    // unofficial
    case Pair(l, r) => signature(l) ++ signature(r)
    // special
    case /*_: NumberObj |*/ Nothing | Anything => Set.empty
  }

  //ensuring (r => r.forall(f => isInstanceOf[Function](f)), "signature of term " + t + " can only be functions")

  /**
   * The signature of a formula, i.e., set of function, predicate, and atomic program 
   * symbols occurring in it.
   */
  def signature(f: Formula): Set[NamedSymbol] = f match {
    // base cases
    case True | False => Set.empty
    case PredOf(p, arg) => Set(p) ++ signature(arg)
    case PredicationalOf(p, arg) => Set(p) ++ signature(arg)
    case DotFormula => Set(DotFormula)
    // pseudo-homomorphic cases
    case Equal(l, r) => signature(l) ++ signature(r)
    case NotEqual(l, r) => signature(l) ++ signature(r)

    case GreaterEqual(l, r) => signature(l) ++ signature(r)
    case Greater(l, r) => signature(l) ++ signature(r)
    case LessEqual(l, r) => signature(l) ++ signature(r)
    case Less(l, r) => signature(l) ++ signature(r)

    // homomorphic cases
    case Not(g) => signature(g)
    case And(l, r) => signature(l) ++ signature(r)
    case Or(l, r) => signature(l) ++ signature(r)
    case Imply(l, r) => signature(l) ++ signature(r)
    case Equiv(l, r) => signature(l) ++ signature(r)

    case Forall(vars, g) => signature(g)
    case Exists(vars, g) => signature(g)

    case Box(p, g) => signature(p) ++ signature(g)
    case Diamond(p, g) => signature(p) ++ signature(g)

    case DifferentialFormula(f) => signature(f)
  }

  /**
   * The signature of a program, i.e., set of function, predicate, and atomic program 
   * symbols occurring in it.
   */
  def signature(p: Program): Set[NamedSymbol] = p match {
    // base cases
    case ap: ProgramConst => Set(ap)
    case ap: DifferentialProgramConst => Set(ap)
    case Assign(x: Variable, e) => signature(e)
    case DiffAssign(xp: DifferentialSymbol, e) => signature(e)
    case AssignAny(x: Variable) => Set.empty
    case Test(f) => signature(f)
    case AtomicODE(xp: DifferentialSymbol, e) => signature(e)
    // homomorphic cases
    case Choice(a, b) => signature(a) ++ signature(b)
    case Compose(a, b) => signature(a) ++ signature(b)
    case Loop(a) => signature(a)
    case ODESystem(a, h) => signature(a) ++ signature(h)
    case DifferentialProduct(a, b) => signature(a) ++ signature(b)
  }

  /**
   * The signature of a sequent.
   */
  def signature(s: Sequent): Set[NamedSymbol] =
    s.ante.foldLeft(Set.empty[NamedSymbol])((a,b)=>a ++ signature(b)) ++
      s.succ.foldLeft(Set.empty[NamedSymbol])((a,b)=>a ++ signature(b))

  /**
   * Any symbols in expression e.
   */
  def symbols(e: Expression): Set[NamedSymbol] = e match {
    case t: Term => symbols(t)
    case f: Formula => symbols(f)
    case a: Program => symbols(a)
  }

  /**
   * Any symbol occurring in term, whether variable or function
   */
  def symbols(t: Term): Set[NamedSymbol] = signature(t) ++ freeVars(t).toSymbolSet

  /**
   * Any symbol occurring in formula, whether free or bound variable or function or predicate or program constant
   * @todo return SetLattice instead?
   */
  def symbols(f: Formula): Set[NamedSymbol] = {
    val stat = apply(f); signature(f) ++ stat.fv.toSymbolSet ++ stat.bv.toSymbolSet
  }

  /**
   * Any symbol occurring in program, whether free or bound variable or function or predicate or program constant
   */
  def symbols(p: Program): Set[NamedSymbol] = {
    val stat = apply(p); signature(p) ++ stat.fv.toSymbolSet ++ stat.bv.toSymbolSet
  }

  /**
   * Any symbol occurring in a sequent, whether free or bound variable or function or predicate or program constant
   */
  def symbols(s: Sequent): Set[NamedSymbol] =
    s.ante.foldLeft(Set[NamedSymbol]())((a,b)=>a ++ symbols(b)) ++
      s.succ.foldLeft(Set[NamedSymbol]())((a,b)=>a ++ symbols(b))
}