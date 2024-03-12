/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
 * Uniform Substitution for KeYmaera X
 * @author
 *   Andre Platzer
 * @author
 *   smitsch
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
 *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
 * @see
 *   Andre Platzer.
 *   [[https://doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]]. In
 *   Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin,
 *   Germany, Proceedings, LNCS. Springer, 2015. [[http://arxiv.org/pdf/1503.01981.pdf arXiv 1503.01981]]
 * @see
 *   Andre Platzer. [[https://doi.org/10.1007/978-3-319-94205-6_15 Uniform substitution for differential game logic]].
 *   In Didier Galmiche, Stephan Schulz and Roberto Sebastiani, editors, Automated Reasoning, 9th International Joint
 *   Conference, IJCAR 2018, volume 10900 of LNCS, pp. 211-227. Springer 2018.
 * @see
 *   Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015.
 *   [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
 * @note
 *   Code Review: 2020-02-17
 */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable
import SetLattice.bottom
import SetLattice.allVars

/**
 * A Uniform Substitution with its application mechanism (original version).
 *
 * A Uniform Substitution uniformly replaces all occurrences of a given predicate p(.) by a formula in (.). It can also
 * replace all occurrences of a function symbol f(.) by a term in (.) and all occurrences of a quantifier symbols C(-)
 * by a formula in (-) and all occurrences of program constant b by a hybrid program.
 *
 * This type implements the application of uniform substitutions to terms, formulas, programs, and sequents.
 *
 * @note
 *   Implements the "global" version that checks admissibility eagerly at bound variables rather than computing bounds
 *   on the fly and checking upon occurrence. Main ingredient of prover core.
 * @note
 *   Superseded by faster alternative [[USubstOne]].
 * @note
 *   soundness-critical
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
 *   Germany, Proceedings, LNCS. Springer, 2015.
 *   [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic. arXiv 1503.01981]]
 * @see
 *   Andre Platzer. [[https://doi.org/10.1007/978-3-319-94205-6_15 Uniform substitution for differential game logic]].
 *   In Didier Galmiche, Stephan Schulz and Roberto Sebastiani, editors, Automated Reasoning, 9th International Joint
 *   Conference, IJCAR 2018, volume 10900 of LNCS, pp. 211-227. Springer 2018.
 * @see
 *   Andre Platzer. [[https://doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015.
 *   [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
 * @see
 *   [[edu.cmu.cs.ls.keymaerax.core.Provable.apply(subst:edu\.cmu\.cs\.ls\.keymaerax\.core\.USubstChurch):edu\.cmu\.cs\.ls\.keymaerax\.core\.Provable*]]
 * @see
 *   [[USubstOne]]
 * @example
 *   Uniform substitution can be applied to a formula
 *   {{{
 *   val p = Function("p", None, Real, Bool)
 *   val x = Variable("x", None, Real)
 *   // p(x) <-> ! ! p(- - x)
 *   val prem = Equiv(PredOf(p, x), Not(Not(PredOf(p, Neg(Neg(x))))))
 *   val s = USubst(Seq(SubstitutionPair(PredOf(p, DotTerm),
 *       GreaterEqual(Power(DotTerm, Number(5)), Number(0)))))
 *   // x^5>=0 <-> !(!((-(-x))^5>=0))
 *   println(s(prem))
 *   }}}
 * @example
 *   Uniform substitutions can be applied via the uniform substitution proof rule to a sequent:
 *   {{{
 *   val p = Function("p", None, Real, Bool)
 *   val x = Variable("x", None, Real)
 *   // p(x) <-> ! ! p(- - x)
 *   val prem = Equiv(PredOf(p, x), Not(Not(PredOf(p, Neg(Neg(x))))))
 *   val s = USubst(Seq(SubstitutionPair(PredOf(p, DotTerm), GreaterEqual(Power(DotTerm, Number(5)), Number(0)))))
 *   val conc = "x^5>=0 <-> !(!((-(-x))^5>=0))".asFormula
 *   val next = UniformSubstitutionRule(s,
 *     Sequent(IndexedSeq(), IndexedSeq(prem)))(
 *       Sequent(IndexedSeq(), IndexedSeq(conc)))
 *   // results in: p(x) <-> ! ! p(- - x)
 *   println(next)
 *   }}}
 * @example
 *   Uniform substitutions also work for substituting hybrid programs
 *   {{{
 *   val p = Function("p", None, Real, Bool)
 *   val x = Variable("x", None, Real)
 *   val a = ProgramConst("a")
 *   // [a]p(x) <-> [a](p(x)&true)
 *   val prem = Equiv(Box(a, PredOf(p, x)), Box(a, And(PredOf(p, x), True)))
 *   val s = USubst(Seq(SubstitutionPair(PredOf(p, DotTerm), GreaterEqual(DotTerm, Number(2))),
 *     SubstitutionPair(a, ODESystem(AtomicODE(DifferentialSymbol(x), Number(5)), True))))
 *   // "[x'=5;]x>=2 <-> [x'=5;](x>=2&true)".asFormula
 *   println(s(prem))
 *   }}}
 * @example
 *   Uniform substitution rule also works when substitution hybrid programs
 *   {{{
 *   val p = Function("p", None, Real, Bool)
 *   val x = Variable("x", None, Real)
 *   val a = ProgramConst("a")
 *   // [a]p(x) <-> [a](p(x)&true)
 *   val prem = Equiv(Box(a, PredOf(p, x)), Box(a, And(PredOf(p, x), True)))
 *   val s = USubst(Seq(SubstitutionPair(PredOf(p, DotTerm), GreaterEqual(DotTerm, Number(2))),
 *     SubstitutionPair(a, ODESystem(AtomicODE(DifferentialSymbol(x), Number(5)), True))))
 *   val conc = "[x'=5;]x>=2 <-> [x'=5;](x>=2&true)".asFormula
 *   val next = UniformSubstitutionRule(s,
 *    Sequent(IndexedSeq(), IndexedSeq(prem)))(
 *      Sequent(IndexedSeq(), IndexedSeq(conc)))
 *   // results in: [x'=5;]x>=2 <-> [x'=5;](x>=2&true)
 *   println(next)
 *   }}}
 */
@deprecated("Use faster USubstOne instead")
final case class USubstChurch(subsDefsInput: immutable.Seq[SubstitutionPair]) extends (Expression => Expression) {

  /**
   * automatically filter out identity substitution no-ops, which can happen by systematic constructions such as
   * unification
   */
  private[this] val subsDefs: immutable.Seq[SubstitutionPair] = subsDefsInput.filter(p => p.what != p.repl)

  insist(noException(dataStructureInvariant()), "unique left-hand sides in substitutees " + this)

  /** unique left hand sides in subsDefs */
  private def dataStructureInvariant(): Unit = {
    // check that we never replace n by something and then again replacing the same n by something
    val lefts = subsDefsInput.map(_.what).toList
    insist(
      lefts.distinct.size == lefts.size,
      "conflict: no duplicate substitutions for the same substitutee " + subsDefsInput,
    )
    // check that we never replace p(x) by something and also p(t) by something
    val lambdaNames = matchKeys
    insist(
      lambdaNames.distinct.size == lambdaNames.size,
      "conflict: no duplicate substitutions for the same substitutee (modulo renaming) " + this,
    )
  }

  override def toString: String = "USubstChurch{" + subsDefs.mkString(", ") + "}"

  /**
   * The (new) free variables that this substitution introduces (without DotTerm/DotFormula arguments). That is the
   * (new) free variables introduced by this substitution, i.e. free variables of all repl that are not bound as
   * arguments in what.
   * @return
   *   union of the freeVars of all our substitution pairs.
   */
  lazy val freeVars: SetLattice[Variable] = subsDefs.foldLeft(bottom[Variable])((a, b) => a ++ b.freeVars)

  /**
   * The signature of the replacement introduced by this substitution.
   * @return
   *   union of the freeVars of all our substitution pairs.
   */
  lazy val signature: immutable.Set[NamedSymbol] = subsDefs.foldLeft(Set.empty[NamedSymbol])((a, b) => a ++ b.signature)

  /**
   * The key characteristic expression constituents that this Substitution is matching on.
   * @return
   *   union of the matchKeys of all our substitution pairs.
   */
  private[core] lazy val matchKeys: immutable.List[NamedSymbol] = subsDefs
    .foldLeft(immutable.List[NamedSymbol]())((a, b) => a :+ b.matchKey)

  // apply calls usubst, augmenting with contract and exception context handling

  def apply(e: Expression): Expression = e match {
    case t: Term => apply(t)
    case f: Formula => apply(f)
    // @note This case happens for standalone uniform substitutions on differential programs such as x'=f() or c as they come up in unification for example.
    case p: DifferentialProgram => apply(p)
    case p: Program => apply(p)
    case f: Function => throw new SubstitutionClashException(
        toString,
        "",
        e + "",
        "",
        "",
        "substitutions are not defined on an isolated Function that is not applied to arguments.",
      )
  }

  // @note could define a direct composition implementation for fast compositions of USubst, but not used.

  /** apply this uniform substitution everywhere in a term */
  // @note optimizable for empty subsDefs if that happens often (unlikely)
  def apply(t: Term): Term = {
    try usubst(t)
    catch { case ex: ProverException => throw ex.inContext(t.prettyString) }
  } ensures
    (
      r => matchKeys.toSet.intersect(StaticSemantics.signature(r) -- signature).isEmpty,
      "Uniform Substitution substituted all occurrences (except when reintroduced by substitution) " + this + "\non" +
        t + "\ngave " + usubst(t),
    )

  /** apply this uniform substitution everywhere in a formula */
  def apply(f: Formula): Formula = {
    try usubst(f)
    catch { case ex: ProverException => throw ex.inContext(f.prettyString) }
  } ensures
    (
      r => matchKeys.toSet.intersect(StaticSemantics.signature(r) -- signature).isEmpty,
      "Uniform Substitution substituted all occurrences (except when reintroduced by substitution) " + this + "\non" +
        f + "\ngave " + usubst(f),
    )

  /** apply this uniform substitution everywhere in a program */
  def apply(p: Program): Program = {
    try usubst(p)
    catch { case ex: ProverException => throw ex.inContext(p.prettyString) }
  } ensures
    (
      r => matchKeys.toSet.intersect(StaticSemantics.signature(r) -- signature).isEmpty,
      "Uniform Substitution substituted all occurrences (except when reintroduced by substitution) " + this + "\non" +
        p + "\ngave " + usubst(p),
    )

  /** apply this uniform substitution everywhere in a differential program */
  def apply(p: DifferentialProgram): DifferentialProgram = {
    try usubst(p)
    catch { case ex: ProverException => throw ex.inContext(p.prettyString) }
  } ensures
    (
      r => matchKeys.toSet.intersect(StaticSemantics.signature(r) -- signature).isEmpty,
      "Uniform Substitution substituted all occurrences (except when reintroduced by substitution) " + this + "\non" +
        p + "\ngave " + usubst(p),
    )

  /** Apply uniform substitution everywhere in the sequent. */
  // @note mapping apply instead of the equivalent usubst makes sure the exceptions are augmented and the ensures contracts checked.
  def apply(s: Sequent): Sequent =
    try { Sequent(s.ante.map(apply), s.succ.map(apply)) }
    catch { case ex: ProverException => throw ex.inContext(s.toString) }

  /**
   * Union of uniform substitutions, i.e., both replacement lists merged.
   * @note
   *   Convenience method not used in the core, but used for stapling uniform substitutions together during unification
   *   etc.
   */
  def ++(other: USubstChurch): USubstChurch = USubstChurch((this.subsDefsInput ++ other.subsDefsInput).distinct)

  /**
   * Whether this substitution matches to replace the given expression e, because there is a substitution pair that
   * matches e.
   */
  @inline
  private def matchHead(e: ApplicationOf): Boolean = subsDefs
    .exists(sp => sp.what.isInstanceOf[ApplicationOf] && sp.sameHead(e))

  // implementation of uniform substitution application
  // @see Figure 1 in Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.

  /** uniform substitution on terms */
  private def usubst(term: Term): Term = {
    term match {
      // uniform substitution base cases
      case x: Variable =>
        assert(!subsDefs.exists(_.what == x), "Substitution of variables not supported: " + x)
        x
      case app @ FuncOf(of, theta) if matchHead(app) =>
        val subs = uniqueElementOf[SubstitutionPair](subsDefs, sp => sp.what.isInstanceOf[FuncOf] && sp.sameHead(app))
        val FuncOf(wf, wArg) = subs.what
        assert(wf == of, "match on same function heads")
        assert(SubstitutionAdmissibility.isSubstitutableArg(wArg))
        // unofficial substitution for Nothing (no effect) and Anything in analogy to substitution for DotTerm
        // @note Uniform substitution of the argument placeholder applied to the replacement subs.repl for the shape subs.what
        USubstChurch(toSubsPairs(wArg, theta)).usubst(subs.repl.asInstanceOf[Term])
      case app @ FuncOf(g: Function, theta) if !matchHead(app) => FuncOf(g, usubst(theta))
      case Nothing =>
        assert(
          !subsDefs.exists(sp => sp.what == Nothing /*&& sp.repl != Nothing*/ ),
          "can replace Nothing only by Nothing, and nothing else",
        );
        Nothing
      case d: DotTerm if subsDefs.exists(_.what == d) => subsDefs.find(_.what == d).get.repl.asInstanceOf[Term]
      case d: DotTerm if !subsDefs.exists(_.what == d) => term
      case n: Number => n
      // @note except for Differential, the following cases are equivalent to f.reapply but are left explicit to enforce revisiting this case when data structure changes.
      // case f:BinaryCompositeTerm => f.reapply(usubst(f.left), usubst(f.right))
      // homomorphic cases
      case Neg(e) => Neg(usubst(e))
      case Plus(l, r) => Plus(usubst(l), usubst(r))
      case Minus(l, r) => Minus(usubst(l), usubst(r))
      case Times(l, r) => Times(usubst(l), usubst(r))
      case Divide(l, r) => Divide(usubst(l), usubst(r))
      case Power(l, r) => Power(usubst(l), usubst(r))
      case Differential(e) =>
        requireAdmissible(allVars, e, term)
        Differential(usubst(e))
      // unofficial
      case Pair(l, r) => Pair(usubst(l), usubst(r))
      case f: UnitFunctional if subsDefs.exists(_.what == f) => subsDefs.find(_.what == f).get.repl.asInstanceOf[Term]
      case f: UnitFunctional if !subsDefs.exists(_.what == f) => f
    }
  } // ensures(r => r.kind==term.kind && r.sort==term.sort, "Uniform Substitution leads to same kind and same sort " + term)

  /** uniform substitution on formulas */
  private def usubst(formula: Formula): Formula = {
    formula match {
      case app @ PredOf(op, theta) if matchHead(app) =>
        val subs = uniqueElementOf[SubstitutionPair](subsDefs, sp => sp.what.isInstanceOf[PredOf] && sp.sameHead(app))
        val PredOf(wp, wArg) = subs.what
        assert(wp == op, "match only if same head")
        assert(SubstitutionAdmissibility.isSubstitutableArg(wArg))
        // unofficial substitution for Nothing (no effect) and Anything in analogy to substitution for DotTerm
        // @note Uniform substitution of the argument placeholder applied to the replacement subs.repl for the shape subs.what
        USubstChurch(toSubsPairs(wArg, theta)).usubst(subs.repl.asInstanceOf[Formula])
      case app @ PredOf(q, theta) if !matchHead(app) => PredOf(q, usubst(theta))
      case app @ PredicationalOf(op, fml) if matchHead(app) =>
        requireAdmissible(allVars, fml, formula)
        val subs =
          uniqueElementOf[SubstitutionPair](subsDefs, sp => sp.what.isInstanceOf[PredicationalOf] && sp.sameHead(app))
        val PredicationalOf(wp, wArg) = subs.what
        assert(wp == op, "match only if same head")
        assert(wArg == DotFormula)
        USubstChurch(SubstitutionPair(wArg, usubst(fml)) :: Nil).usubst(subs.repl.asInstanceOf[Formula])
      case app @ PredicationalOf(q, fml) if !matchHead(app) =>
        // @note admissibility is required for nonmatching predicationals since the arguments might be evaluated in different states.
        requireAdmissible(allVars, fml, formula)
        PredicationalOf(q, usubst(fml))
      case DotFormula if subsDefs.exists(_.what == DotFormula) =>
        subsDefs.find(_.what == DotFormula).get.repl.asInstanceOf[Formula]
      case DotFormula if !subsDefs.exists(_.what == DotFormula) => DotFormula
      case True | False => formula

      // @note except for DifferentialFormula, the following cases are equivalent to f.reapply but are left explicit to enforce revisiting this case when data structure changes.
      // case f:BinaryCompositeTerm => f.reapply(usubst(f.left), usubst(f.right))

      // pseudo-homomorphic cases
      case Equal(l, r) => Equal(usubst(l), usubst(r))
      case NotEqual(l, r) => NotEqual(usubst(l), usubst(r))
      case GreaterEqual(l, r) => GreaterEqual(usubst(l), usubst(r))
      case Greater(l, r) => Greater(usubst(l), usubst(r))
      case LessEqual(l, r) => LessEqual(usubst(l), usubst(r))
      case Less(l, r) => Less(usubst(l), usubst(r))

      // homomorphic cases
      case Not(g) => Not(usubst(g))
      case And(l, r) => And(usubst(l), usubst(r))
      case Or(l, r) => Or(usubst(l), usubst(r))
      case Imply(l, r) => Imply(usubst(l), usubst(r))
      case Equiv(l, r) => Equiv(usubst(l), usubst(r))

      // NOTE DifferentialFormula in analogy to Differential
      case DifferentialFormula(g) =>
        requireAdmissible(allVars, g, formula)
        DifferentialFormula(usubst(g))

      // binding cases add bound variables to u
      case Forall(vars, g) =>
        requireAdmissible(SetLattice(vars), g, formula)
        Forall(vars, usubst(g))
      case Exists(vars, g) =>
        requireAdmissible(SetLattice(vars), g, formula)
        Exists(vars, usubst(g))

      // Note could optimize speed by avoiding duplicate computation unless Scalac knows about CSE
      case Box(p, g) =>
        requireAdmissible(StaticSemantics(usubst(p)).bv, g, formula)
        Box(usubst(p), usubst(g))
      case Diamond(p, g) =>
        requireAdmissible(StaticSemantics(usubst(p)).bv, g, formula)
        Diamond(usubst(p), usubst(g))
      case p: UnitPredicational if subsDefs.exists(_.what == p) =>
        subsDefs.find(_.what == p).get.repl.asInstanceOf[Formula]
      case p: UnitPredicational if !subsDefs.exists(_.what == p) => p
    }
  } // ensures(r => r.kind==formula.kind && r.sort==formula.sort, "Uniform Substitution leads to same kind and same sort " + formula)

  /** uniform substitution on programs */
  private def usubst(program: Program): Program = {
    program match {
      case a: ProgramConst if subsDefs.exists(_.what == a) => subsDefs.find(_.what == a).get.repl.asInstanceOf[Program]
      case a: ProgramConst if !subsDefs.exists(_.what == a) => a
      case a: SystemConst if subsDefs.exists(_.what == a) => subsDefs.find(_.what == a).get.repl.asInstanceOf[Program]
      case a: SystemConst if !subsDefs.exists(_.what == a) => a
      case Assign(x, e) => Assign(x, usubst(e))
      case a: AssignAny => a
      case Test(f) => Test(usubst(f))
      case ODESystem(ode, h) =>
        // @note requireAdmissible(StaticSemantics(usubst(ode, SetLattice.bottom)).bv, ...) would be sound just more permissive
        requireAdmissible(StaticSemantics(ode).bv, h, program)
        ODESystem(usubst(ode), usubst(h))
      case Choice(a, b) => Choice(usubst(a), usubst(b))
      case Compose(a, b) =>
        requireAdmissible(StaticSemantics(usubst(a)).bv, b, program)
        Compose(usubst(a), usubst(b))
      case Loop(a) =>
        requireAdmissible(StaticSemantics(usubst(a)).bv, a, program)
        Loop(usubst(a))
      case Dual(a) => Dual(usubst(a))
    }
  } // ensures(r => r.kind==program.kind && r.sort==program.sort, "Uniform Substitution leads to same kind and same sort " + program)

  /** uniform substitution on differential programs */
  private def usubst(ode: DifferentialProgram): DifferentialProgram = {
    // @note This case is a mixture of AtomicODE and ProgramConst. Only admissibility wrt BV still bound in the result (after substitution of DifferentialProgramConst) but admissible within the whole system simultaneously.
    // @note Conceptually easiest (albeit suboptimally efficient): pre-substitute without taboos to determine BV, then check admissibility during the proper substitution w.r.t. those BV as in other cases.
    requireAdmissible(StaticSemantics(usubstODE(ode, SetLattice.bottom)).bv, ode, ode)
    // @note the requires checking within usubstODE(ode, odeBV) will be redundant but locally the right thing to do.
    // @note usubstODE(ode, StaticSemantics(usubstODE(ode, SetLattice.bottom)).bv) would be sound just more permissive
    usubstODE(ode, StaticSemantics(ode).bv)
  } // ensures(r => r.kind==ode.kind && r.sort==ode.sort, "Uniform Substitution leads to same kind and same sort " + ode)

  /**
   * uniform substitutions on differential programs
   * @param odeBV
   *   the bound variables of the whole ODESystem within which ode occurs, so all odeBV are taboo during the
   *   substitution.
   */
  private def usubstODE(ode: DifferentialProgram, odeBV: SetLattice[Variable]): DifferentialProgram = {
    ode match {
      case AtomicODE(xp: DifferentialSymbol, e) =>
        requireAdmissible(odeBV, e, ode)
        AtomicODE(xp, usubst(e))
      case c: DifferentialProgramConst if subsDefs.exists(_.what == c) =>
        // @note Space compliance already checked in SubstitutionPair construction.
        subsDefs.find(_.what == c).get.repl.asInstanceOf[DifferentialProgram]
      case c: DifferentialProgramConst if !subsDefs.exists(_.what == c) => c
      // homomorphic cases
      case DifferentialProduct(a, b) => DifferentialProduct(usubstODE(a, odeBV), usubstODE(b, odeBV))
    }
  } // ensures(r => r.kind==ode.kind && r.sort==ode.sort, "Uniform Substitution leads to same kind and same sort " + ode)

  /**
   * Turns matching terms into substitution pairs (traverses pairs to create component-wise substitutions).
   * @return
   *   The SubstitutionPair `w ~> usubst(r)` or such substitutions on the components in case w and r are Pairs.
   */
  private def toSubsPairs(w: Term, r: Term): List[SubstitutionPair] = (w, r) match {
    case (Pair(wl, wr), Pair(rl, rr)) => toSubsPairs(wl, rl) ++ toSubsPairs(wr, rr)
    case _ => SubstitutionPair(w, usubst(r)) :: Nil
  }

  // admissibility

  /** Is this uniform substitution U-admissible for expression e? */
  @inline
  private def admissible(U: SetLattice[Variable], e: Expression): Boolean = admissible(U, StaticSemantics.signature(e))

  /**
   * Require that this uniform substitution is U-admissible for expression e, and raise informative exception if not.
   */
  @inline
  private def requireAdmissible(U: SetLattice[Variable], e: Expression, context: Expression): Unit =
    if (!admissible(U, e)) throw SubstitutionClashException(
      toString,
      U.prettyString,
      e.prettyString,
      context.prettyString,
      clashSet(U, e).prettyString,
      "",
    )

  /**
   * check whether this substitution is U-admissible for an expression with the given occurrences of
   * functions/predicates symbols.
   * @param U
   *   taboo list of variables
   * @param occurrences
   *   the function and predicate symbols occurring in the expression of interest.
   * @see
   *   Definition 19 in Andre Platzer.
   *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
   *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
   * @see
   *   arXiv:1503.01981 Definition 12.
   */
  @inline
  private def admissible(U: SetLattice[Variable], occurrences: immutable.Set[NamedSymbol]): Boolean =
    // U-admissible iff FV(restrict this to occurrences) /\ U = empty
    clashSet(U, occurrences).isEmpty
  // this + " is " + U + "-admissible iff restriction " + projection(occurrences) + " to occurring symbols " + occurrences + " has no free variables " + projection(occurrences).freeVars + " of " + U)

  /**
   * Compute the set of all symbols for which this substitution clashes because it is not U-admissible for the given
   * expression.
   * @param U
   *   taboo list of variables
   * @param e
   *   the expression of interest.
   * @return
   *   FV(restrict this to occurrences) /\ U
   * @see
   *   Definition 19 in Andre Platzer.
   *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
   *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
   * @see
   *   arXiv:1503.01981 Definition 12.
   * @note
   *   not used often
   */
  @inline
  private def clashSet(U: SetLattice[Variable], e: Expression): SetLattice[Variable] =
    clashSet(U, StaticSemantics.signature(e))

  /**
   * Compute the set of all symbols for which this substitution clashes because it is not U-admissible for an expression
   * with the given occurrences of functions/predicates symbols.
   * @param U
   *   taboo list of variables
   * @param occurrences
   *   the function and predicate symbols occurring in the expression of interest.
   * @return
   *   FV(restrict this to occurrences) /\ U
   * @see
   *   Definition 19 in Andre Platzer.
   *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
   *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
   * @see
   *   arXiv:1503.01981 Definition 12.
   */
  @inline
  private def clashSet(U: SetLattice[Variable], occurrences: immutable.Set[NamedSymbol]): SetLattice[Variable] =
    projection(occurrences).freeVars.intersect(U)

  /**
   * Projects / restricts a substitution to only those that affect the symbols listed in occurrences.
   * @see
   *   Definition 19 in Andre Platzer.
   *   [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]].
   *   Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
   * @see
   *   arXiv:1503.01981 Definition 12.
   */
  @inline
  private def projection(affected: immutable.Set[NamedSymbol]): USubstChurch =
    new USubstChurch(subsDefs.filter(sigma => affected.contains(sigma.matchKey)))

  /**
   * Get the unique element in c to which pred applies. Protests if that element is not unique because pred applies to
   * more than one element in c or if there is none.
   */
  @inline
  private def uniqueElementOf[E](c: Iterable[E], pred: E => Boolean): E = {
    // require(c.count(pred) == 1, "unique element expected in " + c.mkString)
    val matching = c.filter(pred)
    require(matching.tail.isEmpty, "unique elemented expected in " + c.mkString)
    matching.head
  }
}
