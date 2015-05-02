/**
 * The static semantics of differential dynamic logic.
 * @author aplatzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaera.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable

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
   * @param bv Bound names (maybe written on some paths)
   * @param mbv Must-bound names (definitely written on all paths).
   */
  sealed case class VCP(fv: SetLattice[NamedSymbol],
                        bv: SetLattice[NamedSymbol],
                        mbv: SetLattice[NamedSymbol])

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
  def freeVars(term: Term): SetLattice[NamedSymbol] = term match {
    // base cases
    case x: Variable => SetLattice(x)
    case xp: DifferentialSymbol => SetLattice(xp)
    case _: Number => bottom
    // Type hierarchy makes the assert superfluous, which is intentional to protect against change.
    case DotTerm => assert(!DotTerm.isInstanceOf[Variable], "DotTerm cannot be a variable (!)"); bottom
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
    case Nothing => bottom
    // Anything represents the list of all variables, which are, thus, free
    case Anything => topVarsDiffVars()
  }

  /**
   * Add ' to a set, i.e. turn all elements x in the lattice into x'
   * @return The set of all x' for which x is in s.
   */
  private[core] def differentialSymbols(s: SetLattice[NamedSymbol]): SetLattice[NamedSymbol] =
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
   * The set BV(f) of bound variables of formula f.
   */
  def boundVars(f: Formula): SetLattice[NamedSymbol] = StaticSemantics(f).bv

  /**
   * The set BV(a) of bound variables of program a.
   */
  def boundVars(a: Program): SetLattice[NamedSymbol] = StaticSemantics(a).bv

  // implementation

  private def fmlVars(formula: Formula): VCF = formula match {
    // base cases
    case Equal(l, r)        => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
    case NotEqual(l, r)     => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)

    case GreaterEqual(l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
    case Greater(l, r)      => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
    case LessEqual(l, r)    => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
    case Less(l, r)         => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)

    case PredOf(p, arg) => VCF(fv = freeVars(arg), bv = bottom)
    // DotFormula is like a reserved Predicational
    case DotFormula => VCF(fv = topVarsDiffVars(), bv = bottom)
    case PredicationalOf(p, arg) => VCF(fv = topVarsDiffVars(), bv = bottom) //@todo bv=topVarsDiffVars?

    // homomorphic cases
    case Not(g)      => val vg = fmlVars(g); VCF(fv = vg.fv, bv = vg.bv)
    case And(l, r)   => val vl = fmlVars(l); val vr = fmlVars(r); VCF(fv = vl.fv ++ vr.fv, bv = vl.bv ++ vr.bv)
    case Or(l, r)    => val vl = fmlVars(l); val vr = fmlVars(r); VCF(fv = vl.fv ++ vr.fv, bv = vl.bv ++ vr.bv)
    case Imply(l, r) => val vl = fmlVars(l); val vr = fmlVars(r); VCF(fv = vl.fv ++ vr.fv, bv = vl.bv ++ vr.bv)
    case Equiv(l, r) => val vl = fmlVars(l); val vr = fmlVars(r); VCF(fv = vl.fv ++ vr.fv, bv = vl.bv ++ vr.bv)

    // quantifier binding cases omit bound vars from fv and add bound variables to bf
    case Forall(vars, g) => val vg = fmlVars(g); VCF(fv = vg.fv -- vars, bv = vg.bv ++ vars)
    case Exists(vars, g) => val vg = fmlVars(g); VCF(fv = vg.fv -- vars, bv = vg.bv ++ vars)

    // modality bounding cases omit must-bound vars from fv and add (may-)bound vars to bv
    case Box(p, g)     => val vp = StaticSemantics(p)
      val vg = fmlVars(g)
      VCF(fv = vp.fv ++ (vg.fv -- vp.mbv), bv = vp.bv ++ vg.bv)
    case Diamond(p, g) => val vp = StaticSemantics(p)
      val vg = fmlVars(g)
      VCF(fv = vp.fv ++ (vg.fv -- vp.mbv), bv = vp.bv ++ vg.bv)

    // special cases
    // NOTE DifferentialFormula in analogy to Differential
    case DifferentialFormula(df) => val vdf = fmlVars(df); VCF(fv = vdf.fv ++ differentialSymbols(vdf.fv), bv = vdf.bv)
    case True | False => VCF(fv = bottom, bv = bottom)
  }

  private def progVars(program: Program): VCP = {
    program match {
      // base cases
      case a: ProgramConst             => VCP(fv = topVarsDiffVars(a), bv = topVarsDiffVars(a), mbv = bottom)
      case a: DifferentialProgramConst => VCP(fv = topVarsDiffVars(a), bv = topVarsDiffVars(a), mbv = bottom)
      case Assign(x, e) => VCP(fv = freeVars(e), bv = SetLattice(x), mbv = SetLattice(x))
      case DiffAssign(xp, e) => VCP(fv = freeVars(e), bv = SetLattice(xp), mbv = SetLattice(xp))
      case Test(f) => VCP(fv = StaticSemantics(f).fv, bv = bottom, mbv = bottom)
      case AtomicODE(xp@DifferentialSymbol(x), e) =>
        VCP(fv = SetLattice[NamedSymbol](x) ++ freeVars(e),
          bv = SetLattice[NamedSymbol](x) ++ SetLattice[NamedSymbol](xp),
          mbv = SetLattice[NamedSymbol](x) ++ SetLattice[NamedSymbol](xp))
      // combinator cases
      case Choice(a, b) => val va = progVars(a); val vb = progVars(b)
        VCP(fv = va.fv ++ vb.fv, bv = va.bv ++ vb.bv, mbv = va.mbv.intersect(vb.mbv))
      case Compose(a, b) => val va = progVars(a); val vb = progVars(b)
        VCP(fv = va.fv ++ (vb.fv -- va.mbv), bv = va.bv ++ vb.bv, mbv = va.mbv ++ vb.mbv)
      case Loop(a) => val va = progVars(a); VCP(fv = va.fv, bv = va.bv, mbv = bottom)

      // special cases
      // NOTE x:=* not mentioned in Definition 9
      case AssignAny(x) => VCP(fv = bottom, bv = SetLattice(x), mbv = SetLattice(x))
      // NOTE system of ODE cases not mentioned in Definition 9
      case ODESystem(a, h) => val va = progVars(a)
        VCP(fv = va.fv ++ StaticSemantics(h).fv, bv = va.bv, mbv = va.mbv)
      case DifferentialProduct(a, b) => val va = progVars(a); val vb = progVars(b)
        VCP(fv = va.fv ++ vb.fv, bv = va.bv ++ vb.bv, mbv = va.mbv ++ vb.mbv)
    }
  } ensuring(r => {
    val VCP(_, bv, mbv) = r; mbv.subsetOf(bv)
  }, "MBV(" + program + ") are a subset of BV(" + program + ")")

  // signature of function, predicate, atomic program symbols

  /**
   * The signature of expression e.
   * @todo change return types or at least implementation types to SortedSet for order stability?
   */
  def signature(e: Expression): immutable.Set[NamedSymbol] = e match {
    case t: Term => signature(t)
    case f: Formula => signature(f)
    case a: Program => signature(a)
  }

  /**
   * The signature of a term, i.e., set of function symbols occurring in it.
   * Disregarding number literals.
   */
  def signature(term: Term): immutable.Set[NamedSymbol] = term match {
    // base cases
    case _: Variable => Set.empty
    case _: DifferentialSymbol => Set.empty
    case _: Number => Set.empty
    case DotTerm => Set(DotTerm)
    case FuncOf(f, arg) => Set(f) ++ signature(arg)
    // homomorphic cases
    case Neg(e) => signature(e)
    case Plus(l, r)   => signature(l) ++ signature(r)
    case Minus(l, r)  => signature(l) ++ signature(r)
    case Times(l, r)  => signature(l) ++ signature(r)
    case Divide(l, r) => signature(l) ++ signature(r)
    case Power(l, r)  => signature(l) ++ signature(r)
    case Differential(e) => signature(e)
    // unofficial
    case Pair(l, r) => signature(l) ++ signature(r)
    // special
    case Nothing => Set.empty
    // Anything is the list of all variables, no function symbols
    case Anything => Set.empty
  }

  /**
   * The signature of a formula, i.e., set of function, predicate, and atomic program 
   * symbols occurring in it.
   */
  def signature(formula: Formula): immutable.Set[NamedSymbol] = formula match {
    // base cases
    case True | False => Set.empty
    case PredOf(p, arg) => Set(p) ++ signature(arg)
    case PredicationalOf(p, arg) => Set(p) ++ signature(arg)
    case DotFormula => Set(DotFormula)
    // pseudo-homomorphic cases
    case Equal(l, r)        => signature(l) ++ signature(r)
    case NotEqual(l, r)     => signature(l) ++ signature(r)

    case GreaterEqual(l, r) => signature(l) ++ signature(r)
    case Greater(l, r)      => signature(l) ++ signature(r)
    case LessEqual(l, r)    => signature(l) ++ signature(r)
    case Less(l, r)         => signature(l) ++ signature(r)

    // homomorphic cases
    case Not(g) => signature(g)
    case And(l, r)   => signature(l) ++ signature(r)
    case Or(l, r)    => signature(l) ++ signature(r)
    case Imply(l, r) => signature(l) ++ signature(r)
    case Equiv(l, r) => signature(l) ++ signature(r)

    case Forall(vars, g) => signature(g)
    case Exists(vars, g) => signature(g)

    case Box(p, g)     => signature(p) ++ signature(g)
    case Diamond(p, g) => signature(p) ++ signature(g)

    case DifferentialFormula(g) => signature(g)
  }

  /**
   * The signature of a program, i.e., set of function, predicate, and atomic program 
   * symbols occurring in it.
   */
  def signature(program: Program): immutable.Set[NamedSymbol] = program match {
    // base cases
    case ap: ProgramConst => Set(ap)
    case ap: DifferentialProgramConst => Set(ap)
    case Assign(x, e) => signature(e)
    case DiffAssign(xp, e) => signature(e)
    case AssignAny(x) => Set.empty
    case Test(f) => signature(f)
    case AtomicODE(xp, e) => signature(e)
    // homomorphic cases
    case Choice(a, b) => signature(a) ++ signature(b)
    case Compose(a, b) => signature(a) ++ signature(b)
    case Loop(a) => signature(a)
    case ODESystem(a, h) => signature(a) ++ signature(h)
    case DifferentialProduct(a, b) => signature(a) ++ signature(b)
  }

  /**
   * Any symbols in expression e.
   */
  def symbols(e: Expression): immutable.Set[NamedSymbol] = e match {
    case t: Term => symbols(t)
    case f: Formula => symbols(f)
    case a: Program => symbols(a)
  }

  /**
   * Any symbol occurring verbatim in term, whether variable or function
   */
  def symbols(t: Term): immutable.Set[NamedSymbol] = signature(t) ++ freeVars(t).toSymbolSet

  /**
   * Any symbol occurring verbatim in formula, whether free or bound variable or function or predicate or program constant
   */
  def symbols(f: Formula): immutable.Set[NamedSymbol] = {
    val stat = StaticSemantics(f); signature(f) ++ stat.fv.toSymbolSet ++ stat.bv.toSymbolSet
  }

  /**
   * Any symbol occurring verbatim in program, whether free or bound variable or function or predicate or program constant
   */
  def symbols(p: Program): immutable.Set[NamedSymbol] = {
    val stat = StaticSemantics(p); signature(p) ++ stat.fv.toSymbolSet ++ stat.bv.toSymbolSet
  }

  // convenience for sequents are unions over their formulas

  /**
   * The set FV(a) of free variables of a sequent.
   */
  def freeVars(s: Sequent): SetLattice[NamedSymbol] =
    s.ante.foldLeft(bottom[NamedSymbol])((a,b)=>a ++ freeVars(b)) ++
      s.succ.foldLeft(bottom[NamedSymbol])((a,b)=>a ++ freeVars(b))

  /**
   * The set BV(a) of bound variables of a sequent.
   */
  def boundVars(s: Sequent): SetLattice[NamedSymbol] =
    s.ante.foldLeft(bottom[NamedSymbol])((a,b)=>a ++ boundVars(b)) ++
      s.succ.foldLeft(bottom[NamedSymbol])((a,b)=>a ++ boundVars(b))

  /**
   * The signature of a sequent.
   */
  def signature(s: Sequent): immutable.Set[NamedSymbol] =
    s.ante.foldLeft(Set.empty[NamedSymbol])((a,b)=>a ++ signature(b)) ++
      s.succ.foldLeft(Set.empty[NamedSymbol])((a,b)=>a ++ signature(b))

  /**
   * Any symbol occurring verbatim in a sequent, whether free or bound variable or function or predicate or program constant
   */
  def symbols(s: Sequent): immutable.Set[NamedSymbol] =
    s.ante.foldLeft(Set[NamedSymbol]())((a,b)=>a ++ symbols(b)) ++
      s.succ.foldLeft(Set[NamedSymbol]())((a,b)=>a ++ symbols(b))
}