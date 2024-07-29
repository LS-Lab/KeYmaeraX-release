/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * The static semantics of differential dynamic logic.
 * @author
 *   Andre Platzer
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]]. In
 *   Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin,
 *   Germany, Proceedings, LNCS. Springer, 2015. [[http://arxiv.org/pdf/1503.01981.pdf arXiv 1503.01981]]
 * @note
 *   Code Review: 2020-02-17
 */
package org.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.annotation.nowarn
import scala.collection.immutable

/**
 * The static semantics of differential dynamic logic. This object defines the static semantics of differential dynamic
 * logic in terms of the free variables and bound variables that expressions have as well as their signatures.
 * @author
 *   Andre Platzer
 * @author
 *   smitsch
 * @note
 *   soundness-critical
 * @see
 *   Section 2.3 in Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]]. In
 *   Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin,
 *   Germany, Proceedings, LNCS. Springer, 2015.
 *   [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic. arXiv 1503.01981]]
 * @example
 *   {{{
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
 *   }}}
 * @see
 *   [[org.keymaerax.infrastruct.StaticSemanticsTools]]
 */
object StaticSemantics {

  import SetLattice.{allVars, bottom}

  /**
   * Variable Categories for Formulas: Structure recording which names are free or bound in a formula.
   *
   * @param fv
   *   Free names (maybe read)
   * @param bv
   *   Bound names (maybe written)
   * @note
   *   The core does not uses bv.
   */
  sealed case class VCF(fv: SetLattice[Variable], bv: SetLattice[Variable]) {

    /** union of two variable categorizer structures for formulas */
    def ++(other: VCF): VCF = VCF(fv ++ other.fv, bv ++ other.bv)
  }

  /**
   * Variable Categories for Programs: Structure recording which names are free, bound, or must-bound in a program.
   *
   * @param fv
   *   Free names (maybe read)
   * @param bv
   *   Bound names (maybe written on some paths)
   * @param mbv
   *   Must-bound names (definitely written on all paths).
   */
  sealed case class VCP(fv: SetLattice[Variable], bv: SetLattice[Variable], mbv: SetLattice[Variable])

  /** Compute the static semantics of term t, i.e., the set of its free variables. */
  def apply(t: Term): SetLattice[Variable] = freeVars(t)

  /** Compute the static semantics of formula f, i.e., its set of free and bound variables. */
  def apply(f: Formula): VCF = fmlVars(f)

  /** Compute the static semantics of program a, i.e., its set of free and bound and must-bound variables. */
  def apply(a: Program): VCP = progVars(a)

  /** The set FV(term) of free variables of `term`. */
  @nowarn("msg=fruitless type test")
  def freeVars(term: Term): SetLattice[Variable] = term match {
    // base cases
    case x: Variable => SetLattice(x)
    case _: Number => bottom
    // Type hierarchy makes the assert superfluous, which is intentional to protect against change.
    case d: DotTerm => assert(!d.isInstanceOf[Variable], "DotTerm cannot be a variable (!)"); bottom
    // @note except for Differential, the following cases are equivalent to f.reapply-style but are left explicit to enforce revisiting this case when data structure changes.
    // case f:BinaryCompositeTerm => freeVars(f.left) ++ freeVars(f.right)
    // homomorphic cases
    case FuncOf(f, arg) => freeVars(arg)
    case Neg(e) => freeVars(e)
    case Plus(l, r) => freeVars(l) ++ freeVars(r)
    case Minus(l, r) => freeVars(l) ++ freeVars(r)
    case Times(l, r) => freeVars(l) ++ freeVars(r)
    case Divide(l, r) => freeVars(l) ++ freeVars(r)
    case Power(l, r) => freeVars(l) ++ freeVars(r)
    // special cases FV((e)') = FV(e) ++ FV(e)'
    case Differential(e) => SetLattice.extendToDifferentialSymbols(freeVars(e))
    // unofficial
    case Pair(l, r) => freeVars(l) ++ freeVars(r)
    case Nothing => bottom
    case f: UnitFunctional => spaceVars(f.space)
  }

  /**
   * Check whether expression e is literally a properly differential term/expression, i.e. mentions differentials or
   * differential symbols free.
   *
   * @note
   *   Only verbatim mentions are counted, so not via indirect Space dependency.
   * @note
   *   (5)' and (c())' will be considered as non-differential terms on account of not mentioning variables, but (x+y)'
   *   is differential.
   * @note
   *   [[AtomicODE]] uses isDifferential to ensure explicit differential equation x'=e has no primes in e.
   * @note
   *   [[ODESystem]] uses isDifferential to ensure explicit differential equation x'=e&Q has no primes in Q.
   * @note
   *   For proper terms (not using Anything), freeVars is finite so .symbols==.toSet, so checks for literally free
   *   DifferentialSymbols.
   */
  def isDifferential(e: Expression): Boolean = freeVars(e).symbols.exists(x => x.isInstanceOf[DifferentialSymbol])

  /** The set FV(f) of free variables of formula f. */
  def freeVars(f: Formula): SetLattice[Variable] = StaticSemantics(f).fv

  /** The set FV(a) of free variables of program a. */
  def freeVars(a: Program): SetLattice[Variable] = StaticSemantics(a).fv

  /** The set FV(e) of free variables of expression e. */
  def freeVars(e: Expression): SetLattice[Variable] = e match {
    case t: Term => freeVars(t)
    case f: Formula => freeVars(f)
    case a: Program => freeVars(a)
    // An isolated Function that has not been applied a FuncOf is no Term and has no free variables
    case f: Function => bottom
  }

  /** The set BV(f) of bound variables of formula f. */
  def boundVars(f: Formula): SetLattice[Variable] = StaticSemantics(f).bv

  /** The set BV(a) of bound variables of program a. */
  def boundVars(a: Program): SetLattice[Variable] = StaticSemantics(a).bv

  /** The set var(e) of variables of expression e, whether free or bound. */
  def vars(e: Expression): SetLattice[Variable] = e match {
    case t: Term => freeVars(t)
    case f: Formula => freeVars(f) ++ boundVars(f)
    case a: Program => freeVars(a) ++ boundVars(a)
    // An isolated Function that has not been applied a FuncOf is no Term and has no variables
    case f: Function => bottom
  }

  // implementation

  private def fmlVars(formula: Formula): VCF = formula match {
    // base cases
    case Equal(l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
    case NotEqual(l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)

    case GreaterEqual(l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
    case Greater(l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
    case LessEqual(l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)
    case Less(l, r) => VCF(fv = freeVars(l) ++ freeVars(r), bv = bottom)

    case PredOf(p, arg) => VCF(fv = freeVars(arg), bv = bottom)
    // @note Could move SpaceDependent to the bottom of the match since core will not be interested in its free variables
    case PredicationalOf(p, arg) => VCF(fv = allVars, bv = allVars)
    // @note DotFormula is like a reserved zero-parameter Predicational. Its bound variables are debatable since it has no child.
    case DotFormula => VCF(fv = allVars, bv = allVars)
    // @note UnitPredicational is a zero-parameter Predicational. Its bound variables are debatable since it has no child.
    case f: UnitPredicational => VCF(fv = spaceVars(f.space), bv = spaceVars(f.space))

    // @note except for DifferentialFormula, the following cases are equivalent to f.reapply-style but are left explicit to enforce revisiting this case when data structure changes.
    // case f:BinaryCompositeFormula => fmlVars(f.left) ++ fmlVars(f.right)
    // homomorphic cases
    case Not(g) => fmlVars(g)
    case And(l, r) => fmlVars(l) ++ fmlVars(r)
    case Or(l, r) => fmlVars(l) ++ fmlVars(r)
    case Imply(l, r) => fmlVars(l) ++ fmlVars(r)
    case Equiv(l, r) => fmlVars(l) ++ fmlVars(r)

    // quantifier binding cases omit bound vars from fv and add bound variables to bf
    case Forall(vars, g) => val vg = fmlVars(g); VCF(fv = vg.fv -- vars, bv = vg.bv ++ vars)
    case Exists(vars, g) => val vg = fmlVars(g); VCF(fv = vg.fv -- vars, bv = vg.bv ++ vars)

    // modality bounding cases omit must-bound vars from fv and add (may-)bound vars to bv
    case Box(p, g) =>
      val vp = StaticSemantics(p)
      val vg = fmlVars(g)
      VCF(fv = vp.fv ++ (vg.fv -- vp.mbv), bv = vp.bv ++ vg.bv)
    case Diamond(p, g) =>
      val vp = StaticSemantics(p)
      val vg = fmlVars(g)
      VCF(fv = vp.fv ++ (vg.fv -- vp.mbv), bv = vp.bv ++ vg.bv)

    // special cases
    // @note DifferentialFormula in analogy to Differential
    case DifferentialFormula(df) =>
      val vdf = fmlVars(df)
      // @note FV(df)++FV(df)' are free. But only BV(df) are bound. E.g., (\forall x x>=y)' still only binds x, not x'.
      VCF(fv = SetLattice.extendToDifferentialSymbols(vdf.fv), bv = vdf.bv)

    case True | False => VCF(fv = bottom, bv = bottom)
  }

  @nowarn("msg=match may not be exhaustive")
  private def progVars(program: Program): VCP = {
    program match {
      // base cases
      case a: ProgramConst => VCP(fv = spaceVars(a.space), bv = spaceVars(a.space), mbv = bottom)
      case a: SystemConst => VCP(fv = spaceVars(a.space), bv = spaceVars(a.space), mbv = bottom)
      case a: DifferentialProgramConst => VCP(fv = spaceVars(a.space), bv = spaceVars(a.space), mbv = bottom)
      case Assign(x, e) => VCP(fv = freeVars(e), bv = SetLattice(x), mbv = SetLattice(x))
      case Test(f) => VCP(fv = StaticSemantics(f).fv, bv = bottom, mbv = bottom)
      case AtomicODE(xp @ DifferentialSymbol(x), e) =>
        VCP(fv = SetLattice(x) ++ freeVars(e), bv = SetLattice(Set(x, xp)), mbv = SetLattice(Set(x, xp)))
      // combinator cases
      case Choice(a, b) =>
        val va = progVars(a); val vb = progVars(b)
        VCP(fv = va.fv ++ vb.fv, bv = va.bv ++ vb.bv, mbv = va.mbv.intersect(vb.mbv))
      case Compose(a, b) =>
        val va = progVars(a); val vb = progVars(b)
        VCP(fv = va.fv ++ (vb.fv -- va.mbv), bv = va.bv ++ vb.bv, mbv = va.mbv ++ vb.mbv)
      case Loop(a) => val va = progVars(a); VCP(fv = va.fv, bv = va.bv, mbv = bottom)
      case Dual(a) => progVars(a)

      // special cases
      // @note x:=* in analogy to x:=e
      case AssignAny(x) => VCP(fv = bottom, bv = SetLattice(x), mbv = SetLattice(x))
      // @note system generalization of x'=e&h
      case ODESystem(a, h) =>
        val va = progVars(a)
        VCP(fv = va.fv ++ StaticSemantics(h).fv, bv = va.bv, mbv = va.mbv)
      case DifferentialProduct(a, b) =>
        val va = progVars(a); val vb = progVars(b)
        VCP(fv = va.fv ++ vb.fv, bv = va.bv ++ vb.bv, mbv = va.mbv ++ vb.mbv)
    }
  } ensures
    (r => { val VCP(_, bv, mbv) = r; mbv.subsetOf(bv) }, "MBV(" + program + ") are a subset of BV(" + program + ")")

  // signature of function, predicate, atomic program symbols

  /**
   * The signature of expression e.
   *
   * @note
   *   Result will not be order stable, so order could be different on different runs of the prover.
   * @example
   *   {{{
   *   signature(e).toList.sort            // sorts by compare of NamedSymbol, by name and index
   *   signature(e).toList.sortBy(_.name)  // sorts alphabetically by name, ignores indices
   *   }}}
   * @note
   *   Soundness-critical in data structure invariant for interpreted functions.
   * @note
   *   Not soundness-critical otherwise since substitution only uses it in old [[USubstChurch]] not in new
   *   [[USubstOne]].
   */
  def signature(e: Expression): immutable.Set[NamedSymbol] = e match {
    case t: Term => signature(t)
    case f: Formula => signature(f)
    case a: Program => signature(a)
    // An isolated Function that has not been applied a FuncOf is no Term but itself still occurs
    case f: Function => Set(f)
  }

  /**
   * The signature of a term, i.e., set of (non-logical) function/functional symbols occurring in it. Disregarding
   * number literals.
   * @note
   *   Soundness-critical in data structure invariant for interpreted functions.
   * @note
   *   Not soundness-critical otherwise since substitution only uses it in old [[USubstChurch]] not in new
   *   [[USubstOne]].
   */
  def signature(term: Term): immutable.Set[NamedSymbol] = term match {
    // base cases
    case _: Variable => Set.empty
    case _: Number => Set.empty
    case FuncOf(f, arg) => Set(f) ++ signature(arg)
    case d: DotTerm => Set(d)
    // @note the following cases are equivalent to f.reapply-style but are left explicit to enforce revisiting this case when data structure changes.
    // case f:BinaryCompositeTerm => signature(f.left) ++ signature(f.right)
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
    case Nothing => Set.empty
    case f: UnitFunctional => Set(f)
  }

  /**
   * The signature of a formula, i.e., set of (non-logical) function, predicate, predicational, and atomic program
   * symbols occurring in it.
   * @note
   *   Soundness-critical in data structure invariant for interpreted functions.
   * @note
   *   Not soundness-critical otherwise since substitution only uses it in old [[USubstChurch]] not in new
   *   [[USubstOne]].
   */
  def signature(formula: Formula): immutable.Set[NamedSymbol] = formula match {
    // base cases
    case True | False => Set.empty
    case PredOf(p, arg) => Set(p) ++ signature(arg)
    case PredicationalOf(p, arg) => Set(p) ++ signature(arg)
    case DotFormula => Set(DotFormula)
    case p: UnitPredicational => Set(p)
    // @note the following cases are equivalent to f.reapply-style but are left explicit to enforce revisiting this case when data structure changes.
    // case f:BinaryCompositeFormula => signature(f.left) ++ signature(f.right)
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

    case DifferentialFormula(g) => signature(g)
  }

  /**
   * The signature of a program, i.e., set of function, predicate, and atomic program symbols occurring in it.
   * @note
   *   Soundness-critical in data structure invariant for interpreted functions.
   * @note
   *   Not soundness-critical otherwise since substitution only uses it in old [[USubstChurch]] not in new
   *   [[USubstOne]].
   */
  @nowarn("msg=match may not be exhaustive")
  def signature(program: Program): immutable.Set[NamedSymbol] = program match {
    // base cases
    case ap: ProgramConst => Set(ap)
    case ap: SystemConst => Set(ap)
    case ap: DifferentialProgramConst => Set(ap)
    case Assign(x, e) => signature(e)
    case AssignAny(x) => Set.empty
    case Test(f) => signature(f)
    case AtomicODE(xp, e) => signature(e)
    // @note the following cases are equivalent to f.reapply-style but are left explicit to enforce revisiting this case when data structure changes.
    // case f:BinaryCompositeProgram => signature(f.left) ++ signature(f.right)
    // homomorphic cases
    case Choice(a, b) => signature(a) ++ signature(b)
    case Compose(a, b) => signature(a) ++ signature(b)
    case Loop(a) => signature(a)
    case Dual(a) => signature(a)
    case ODESystem(a, h) => signature(a) ++ signature(h)
    case DifferentialProduct(a, b) => signature(a) ++ signature(b)
  }

  /**
   * Any (non-logical) symbols occurring verbatim in expression e, whether free or bound variable or function or
   * predicate or program constant.
   */
  def symbols(e: Expression): immutable.Set[NamedSymbol] = e match {
    case t: Term => symbols(t)
    case f: Formula => symbols(f)
    case a: Program => symbols(a)
    // An isolated Function that has not been applied a FuncOf is no Term and has no variables but itself still occurs
    case f: Function => Set(f)
  }

  /** Any (non-logical) symbol occurring verbatim in term, whether variable or function. */
  def symbols(t: Term): immutable.Set[NamedSymbol] = signature(t) ++ freeVars(t).symbols

  /**
   * Any (non-logical) symbol occurring verbatim in formula, whether free or bound variable or function or predicate or
   * program constant.
   */
  def symbols(f: Formula): immutable.Set[NamedSymbol] = {
    val stat = StaticSemantics(f)
    signature(f) ++ stat.fv.symbols ++ stat.bv.symbols
  }

  /**
   * Any (non-logical) symbol occurring verbatim in program, whether free or bound variable or function or predicate or
   * program constant.
   */
  def symbols(p: Program): immutable.Set[NamedSymbol] = {
    // @note stat.mbv subset of stat.bv so no point in adding them
    val stat = StaticSemantics(p)
    signature(p) ++ stat.fv.symbols ++ stat.bv.symbols
  }

  // convenience for sequents are unions over their formulas

  /** The set FV(a) of free variables of a sequent. */
  def freeVars(s: Sequent): SetLattice[Variable] = (s.ante ++ s.succ)
    .foldLeft(bottom[Variable])((a, b) => a ++ freeVars(b))

  /** The set BV(a) of bound variables of a sequent. */
  def boundVars(s: Sequent): SetLattice[Variable] = (s.ante ++ s.succ)
    .foldLeft(bottom[Variable])((a, b) => a ++ boundVars(b))

  /** The signature of a sequent. */
  def signature(s: Sequent): immutable.Set[NamedSymbol] = (s.ante ++ s.succ)
    .foldLeft(Set.empty[NamedSymbol])((a, b) => a ++ signature(b))

  /**
   * Any symbol occurring verbatim in a sequent, whether free or bound variable or function or predicate or program
   * constant
   */
  def symbols(s: Sequent): immutable.Set[NamedSymbol] = (s.ante ++ s.succ)
    .foldLeft(Set[NamedSymbol]())((a, b) => a ++ symbols(b))

  // helpers

  /**
   * The sequence of taboo and taboo' for all taboo in taboos, with taboo' only included for non-differential and real
   * variables taboo
   */
  private[core] def spaceTaboos(taboos: immutable.Seq[Variable]): immutable.Seq[Variable] = taboos.flatMap(taboo =>
    if (taboo.isInstanceOf[DifferentialSymbol] || taboo.sort != Real) immutable.Seq(taboo)
    else immutable.Seq(taboo, DifferentialSymbol(taboo))
  )

  /**
   * The variables and differential symbols that are in the given state space.
   * @param space
   *   The state space whose set (lattice) of variables and differential variables to compute.
   *   - `AnyArg` returns the [[SetLattice.allVars]].
   *   - `Except(taboo)` returns all variables except [[spaceTaboos]](taboos), i.e. all variables and differential
   *     variables except the taboo x and x'.
   */
  def spaceVars(space: Space): SetLattice[Variable] = space match {
    case AnyArg => SetLattice.allVars
    case Except(taboos) =>
      // @note this assumes no higher-order differential symbols
      CoFiniteSet(spaceTaboos(taboos).toSet, Set.empty)
  }

}
