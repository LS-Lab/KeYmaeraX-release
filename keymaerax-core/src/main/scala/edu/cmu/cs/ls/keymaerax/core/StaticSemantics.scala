/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * The static semantics of differential dynamic logic.
 * @author Andre Platzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, volume 9195 of LNCS, pages 467-481. Springer, 2015. arXiv 1503.01981, 2015."
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable

/**
 * The static semantics of differential dynamic logic.
 * This object defines the static semantics of differential dynamic logic
 * in terms of the free variables and bound variables that expressions have as well as their signatures.
 * See [[http://arxiv.org/pdf/1503.01981.pdf Section 2.3]]
 * @author Andre Platzer
 * @author smitsch
 * @note soundness-critical
 * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
 * @example
 * {{{
 *   val fml = Imply(Greater(Variable("x",None,Real), Number(5)),
 *     Forall(Seq(Variable("y",None,Real)),
 *       GreaterEqual(Variable("x",None,Real), FuncOf(Function("f",None,Real,Real), Variable("y",None,Real)))))
 *   // determine the static semantics of the above formula
 *   val stat = StaticSemantics(fml)
 *   println("Free variables  " + stat.fv)
 *   println("Bound variables " + stat.bv)
 *   // determine all function, predicate and program constants occurring in the above formula
 *   println("Signature       " + StaticSemantics.signature(fml))
 *   // determine all symbols occurring in the above formula
 *   println("Symbols         " + StaticSemantics.symbols(fml))
 * }}}
 * @see [[edu.cmu.cs.ls.keymaerax.tactics.StaticSemanticsTools]]
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
    case Neg(e)       => freeVars(e)
    case Plus(l, r)   => freeVars(l) ++ freeVars(r)
    case Minus(l, r)  => freeVars(l) ++ freeVars(r)
    case Times(l, r)  => freeVars(l) ++ freeVars(r)
    case Divide(l, r) => freeVars(l) ++ freeVars(r)
    case Power(l, r)  => freeVars(l) ++ freeVars(r)
    // special cases
    case Differential(e) => SetLattice.extendToDifferentialSymbols(freeVars(e))
    // unofficial
    case Pair(l, r)   => freeVars(l) ++ freeVars(r)
    case Nothing      => bottom
    // Anything represents the list of all variables, which are, thus, free
    case Anything     => topVarsDiffVars()
  }

  /**
   * Check whether expression e is a properly differential term/expression, i.e. mentions differentials or differential symbols.
   * @note Only verbatim mentions are counted, so not via Anything.
   */
  def isDifferential(e: Expression): Boolean = freeVars(e).toSymbolSet.exists(x => x.isInstanceOf[DifferentialSymbol])

  /**
   * The set FV(f) of free variables of formula f.
   */
  def freeVars(f: Formula): SetLattice[NamedSymbol] = StaticSemantics(f).fv

  /**
   * The set FV(a) of free variables of program a.
   */
  def freeVars(a: Program): SetLattice[NamedSymbol] = StaticSemantics(a).fv

  /**
   * The set FV(e) of free variables of expression e.
   */
  def freeVars(e: Expression): SetLattice[NamedSymbol] = e match {
    case t: Term => freeVars(t)
    case f: Formula => freeVars(f)
    case a: Program => freeVars(a)
  }

  /**
   * The set BV(f) of bound variables of formula f.
   */
  def boundVars(f: Formula): SetLattice[NamedSymbol] = StaticSemantics(f).bv

  /**
   * The set BV(a) of bound variables of program a.
   */
  def boundVars(a: Program): SetLattice[NamedSymbol] = StaticSemantics(a).bv

  /** The set var(e) of variables of expression e, whether free or bound. */
  def vars(e: Expression): SetLattice[NamedSymbol] = e match {
    case t: Term => freeVars(t)
    case f: Formula => freeVars(f) ++ boundVars(f)
    case a: Program => freeVars(a) ++ boundVars(a)
  }


  // implementation

  private def fmlVars(formula: Formula): VCF = formula match {
    // base cases
    case Equal(l, r)        => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
    case NotEqual(l, r)     => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)

    case GreaterEqual(l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
    case Greater(l, r)      => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
    case LessEqual(l, r)    => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
    case Less(l, r)         => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)

    case PredOf(p, arg)     => VCF(fv = freeVars(arg), bv = bottom)
    case PredicationalOf(p, arg) => VCF(fv = topVarsDiffVars(), bv = topVarsDiffVars())
    //@note DotFormula is like a reserved zero-parameter Predicational
    case DotFormula         => VCF(fv = topVarsDiffVars(), bv = topVarsDiffVars())

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
    case Box(p, g)     =>
      val vp = StaticSemantics(p)
      val vg = fmlVars(g)
      VCF(fv = vp.fv ++ (vg.fv -- vp.mbv), bv = vp.bv ++ vg.bv)
    case Diamond(p, g) =>
      val vp = StaticSemantics(p)
      val vg = fmlVars(g)
      VCF(fv = vp.fv ++ (vg.fv -- vp.mbv), bv = vp.bv ++ vg.bv)

    // special cases
    //@note DifferentialFormula in analogy to Differential
    case DifferentialFormula(df) =>
      val vdf = fmlVars(df)
      VCF(fv = SetLattice.extendToDifferentialSymbols(vdf.fv), bv = vdf.bv)

    case True | False => VCF(fv = bottom, bv = bottom)
  }

  private def progVars(program: Program): VCP = {
    program match {
      // base cases
      case a: ProgramConst             => VCP(fv = topVarsDiffVars(), bv = topVarsDiffVars(), mbv = bottom)
      case a: DifferentialProgramConst => VCP(fv = topVarsDiffVars(), bv = topVarsDiffVars(), mbv = bottom)
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
      case Dual(a) => val va = progVars(a); VCP(fv = va.fv, bv = va.bv, mbv = va.mbv)

      // special cases
      //@note x:=* in analogy to x:=e
      case AssignAny(x) => VCP(fv = bottom, bv = SetLattice(x), mbv = SetLattice(x))
      //@note system generalization of x'=e&h
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
   * @note Result will not be order stable, so order could be different on different runs of the prover.
   * @example{{{
   *    signature(e).toList.sort            // sorts by compare of NamedSymbol, by name and index
   *    signature(e).toList.sortBy(_.name)  // sorts alphabetically by name, ignores indices
   * }}}
   */
  def signature(e: Expression): immutable.Set[NamedSymbol] = e match {
    case t: Term => signature(t)
    case f: Formula => signature(f)
    case a: Program => signature(a)
  }

  /**
   * The signature of a term, i.e., set of (non-logical) function symbols occurring in it.
   * Disregarding number literals.
   */
  def signature(term: Term): immutable.Set[NamedSymbol] = term match {
    // base cases
    case _: Variable => Set.empty
    case _: DifferentialSymbol => Set.empty
    case _: Number => Set.empty
    case FuncOf(f, arg) => Set(f) ++ signature(arg)
    case DotTerm => Set(DotTerm)
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
   * The signature of a formula, i.e., set of (non-logical) function, predicate, and atomic program
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
    case Assign(x, e)     => signature(e)
    case DiffAssign(xp, e) => signature(e)
    case AssignAny(x)     => Set.empty
    case Test(f)          => signature(f)
    case AtomicODE(xp, e) => signature(e)
    // homomorphic cases
    case Choice(a, b)     => signature(a) ++ signature(b)
    case Compose(a, b)    => signature(a) ++ signature(b)
    case Loop(a)          => signature(a)
    case Dual(a)          => signature(a)
    case ODESystem(a, h)  => signature(a) ++ signature(h)
    case DifferentialProduct(a, b) => signature(a) ++ signature(b)
  }

  /**
   * Any (non-logical) symbols occurring verbatim in expression e, whether free or bound variable or function or predicate or program constant.
   */
  def symbols(e: Expression): immutable.Set[NamedSymbol] = e match {
    case t: Term => symbols(t)
    case f: Formula => symbols(f)
    case a: Program => symbols(a)
  }

  /**
   * Any (non-logical) symbol occurring verbatim in term, whether variable or function.
   */
  def symbols(t: Term): immutable.Set[NamedSymbol] = signature(t) ++ freeVars(t).toSymbolSet

  /**
   * Any (non-logical) symbol occurring verbatim in formula, whether free or bound variable or function or predicate or program constant.
   */
  def symbols(f: Formula): immutable.Set[NamedSymbol] = {
    val stat = StaticSemantics(f); signature(f) ++ stat.fv.toSymbolSet ++ stat.bv.toSymbolSet
  }

  /**
   * Any (non-logical) symbol occurring verbatim in program, whether free or bound variable or function or predicate or program constant.
   */
  def symbols(p: Program): immutable.Set[NamedSymbol] = {
    //@note stat.mbv subset of stat.bv so no point in adding them
    val stat = StaticSemantics(p); signature(p) ++ stat.fv.toSymbolSet ++ stat.bv.toSymbolSet
  }

  // convenience for sequents are unions over their formulas

  /**
   * The set FV(a) of free variables of a sequent.
   */
  def freeVars(s: Sequent): SetLattice[NamedSymbol] =
    (s.ante ++ s.succ).foldLeft(bottom[NamedSymbol])((a,b)=>a ++ freeVars(b))

  /**
   * The set BV(a) of bound variables of a sequent.
   */
  def boundVars(s: Sequent): SetLattice[NamedSymbol] =
    (s.ante ++ s.succ).foldLeft(bottom[NamedSymbol])((a,b)=>a ++ boundVars(b))

  /**
   * The signature of a sequent.
   */
  def signature(s: Sequent): immutable.Set[NamedSymbol] =
    (s.ante ++ s.succ).foldLeft(Set.empty[NamedSymbol])((a,b)=>a ++ signature(b))

  /**
   * Any symbol occurring verbatim in a sequent, whether free or bound variable or function or predicate or program constant
   */
  def symbols(s: Sequent): immutable.Set[NamedSymbol] =
    (s.ante ++ s.succ).foldLeft(Set[NamedSymbol]())((a,b)=>a ++ symbols(b))
}