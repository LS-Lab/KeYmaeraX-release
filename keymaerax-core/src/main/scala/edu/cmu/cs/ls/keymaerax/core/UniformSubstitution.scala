/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
/**
  * Uniform Substitution for KeYmaera X
  * @author Andre Platzer
  * @author smitsch
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015. [[http://arxiv.org/pdf/1503.01981.pdf arXiv 1503.01981]]
  * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
  * @note Code Review: 2016-03-09
  */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable

import SetLattice.bottom
import SetLattice.allVars


/**
  * Representation of a substitution replacing `what` with `repl` uniformly, everywhere.
  *
  * @param what the expression to be replaced. `what` can have one of the following forms:
  *          - [[PredOf]](p:[[Function]], [[DotTerm]]/[[Nothing]])
  *          - [[FuncOf]](f:[[Function]], [[DotTerm]]/[[Nothing]])
  *          - [[ProgramConst]] or [[DifferentialProgramConst]]
  *          - [[UnitPredicational]]
  *          - [[UnitFunctional]]
  *          - [[PredicationalOf]](p:[[Function]], [[DotFormula]])
  *          - [[DotTerm]]
  *          - [[DotFormula]]
  * @param repl the expression to be used in place of `what`.
  * @requires what.kind==repl.kind && what.sort==repl.sort && what has an acceptable shpe
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
  */
final case class SubstitutionPair (what: Expression, repl: Expression) {
  insist(what.kind == repl.kind, "Substitution to same kind of expression (terms for terms, formulas for formulas, programs for programs): " + this + " substitutes " + what.kind + " ~> " + repl.kind)
  insist(what.sort == repl.sort, "Sorts have to match in substitution pairs: " + this + " substitutes " + what.sort + " ~> " + repl.sort)
  assert(what match {
    case _: Term    => repl.isInstanceOf[Term]
    case _: Formula => repl.isInstanceOf[Formula]
    case _: Program => repl.isInstanceOf[Program]
  }, "(redundant test) substitution to same kind of expression (terms for terms, formulas for formulas, programs for programs) " + this + " substitutes " + what.kind + " ~> " + repl.kind)
  insist(noException(matchKey), "Substitutable expression expected: " + this)
  insist(what match {
    case sp: SpaceDependent => sp.space match {
      case AnyArg        => true
      case Except(taboo) =>
        //@note this assumes that only sort Real is ever used for taboos, for simplicity.
        val taboos = SetLattice(Set(taboo, DifferentialSymbol(taboo)))
        sp match {
          //@note by previous insists, repl has to be a DifferentialProgram
          case _: DifferentialProgramConst => val vc = StaticSemantics(repl.asInstanceOf[DifferentialProgram])
            vc.fv.intersect(taboos).isEmpty && vc.bv.intersect(taboos).isEmpty
          case _: UnitPredicational => StaticSemantics.freeVars(repl).intersect(taboos).isEmpty
          case _: UnitFunctional    => StaticSemantics.freeVars(repl).intersect(taboos).isEmpty
      }
    }
    // only space-dependents have space-compatibility requirements
    case _ => true
  }, "Space-compatible substitution expected: " + this
  )

  /**
    * The (new) free variables that this substitution introduces (without DotTerm/DotFormula arguments).
    * That is the (new) free variables introduced by this substitution, i.e. free variables of repl that are not bound as arguments in what.
    * @return essentially freeVars(repl) except for special handling of UnitFunctional and UnitPredicational arguments.
    * @see Definition 19 in Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
    */
  lazy val freeVars: SetLattice[Variable] = what match {
    //@note semantic state-dependent symbols have no free variables.
    case what: StateDependent => what match {
      // unit functionals are like Predicationals
      // predicationals are not function nor predicate symbols
      // DotFormula is a nullary Predicational
      // unit predicationals are nullary Predicationals
      // program constants are always admissible, since their meaning doesn't depend on state
      // DifferentialProgramConst are handled in analogy to program constants, since space-compatibility already checked
      case UnitFunctional(_, _, _) | UnitPredicational(_, _) | PredicationalOf(_, DotFormula) | DotFormula |
           ProgramConst(_) | DifferentialProgramConst(_, _) => bottom
    }
    case _ => StaticSemantics.freeVars(repl)
  }

  /**
    * The signature of the replacement introduced by this substitution.
    * @note DotTerm and DotFormula arguments don't literally occur if bound by p(DotTerm) ~> DotTerm>5
    */
  lazy val signature: immutable.Set[NamedSymbol] = what match {
    case what: ApplicationOf => what match {
      case FuncOf(_, d: DotTerm) => StaticSemantics.signature(repl) - d
      case PredOf(_, d: DotTerm) => StaticSemantics.signature(repl) - d
      case PredicationalOf(_, DotFormula) => StaticSemantics.signature(repl) - DotFormula
      case _ => StaticSemantics.signature(repl)
    }
    case _ => StaticSemantics.signature(repl)
  }

  /**
    * Occurrences of what symbol this SubstitutionPair will be replacing.
    * @return Function/predicate/predicational or DotTerm or (Differential)ProgramConst whose occurrences we will replace.
    * @note Checks that what is a substitutable expression.
    */
  private[core] lazy val matchKey: NamedSymbol = what match {
    case p: UnitPredicational        => p
    case f: UnitFunctional           => f
    case a: ProgramConst             => a
    case a: DifferentialProgramConst => a
    case PredOf(p: Function, DotTerm(_) | Nothing) if !p.interpreted => p
    case FuncOf(f: Function, DotTerm(_) | Nothing) if !f.interpreted => f
    case PredicationalOf(p: Function, DotFormula)  if !p.interpreted => p
    case d: DotTerm                  => d
    case DotFormula                  => DotFormula
    case Nothing => assert(repl == Nothing, "can replace Nothing only by Nothing, and nothing else"); Nothing // it makes no sense to substitute Nothing
    case _ => throw new CoreException("Nonsubstitutable expression " + this)
  }

  /**
    * Check whether we match on the term other, i.e. both have the same head so the occurrence in other
    * should be replaced according to this SubstitutionPair.
    */
  private[core] def sameHead(other: ApplicationOf): Boolean = what match {
    case FuncOf(lf, arg) =>
      assert(arg match { case DotTerm(_) | Nothing => true case _ => false }, "Only DotTerm/Nothing allowed as argument")
      other match { case FuncOf(rf, _) => lf == rf case _ => false }
    case PredOf(lf, arg) =>
      assert(arg match { case DotTerm(_) | Nothing => true case _ => false }, "Only DotTerm/Nothing allowed as argument")
      other match { case PredOf(rf, _) => lf == rf case _ => false }
    case PredicationalOf(lf, arg) =>
      assert(arg match { case DotFormula => true case _ => false }, "Only DotFormula allowed as argument")
      other match { case PredicationalOf(rf, _) => lf == rf case _ => false }
    case _ => assert(false, "sameHead only used for ApplicationOf"); false
  }

  override def toString: String = "(" + what.prettyString + "~>" + repl.prettyString + ")"
}



/**
  * A Uniform Substitution with its application mechanism.
  * A Uniform Substitution uniformly replaces all occurrences of a given predicate p(.) by a formula in (.).
  * It can also replace all occurrences of a function symbol f(.) by a term in (.)
  * and all occurrences of a quantifier symbols C(-) by a formula in (-)
  * and all occurrences of program constant b by a hybrid program.
  *
  * This type implements the application of uniform substitutions to terms, formulas, programs, and sequents.
  * @note Implements the "global" version that checks admissibility eagerly at bound variables rather than computing bounds on the fly and checking upon occurrence.
  * Main ingredient of prover core.
  * @note soundness-critical
  * @author Andre Platzer
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
  * @see Andre Platzer. [[http://dx.doi.org/10.1007/978-3-319-21401-6_32 A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
  * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
  * @see Andre Platzer. [[http://dx.doi.org/10.1145/2817824 Differential game logic]]. ACM Trans. Comput. Log. 17(1), 2015. [[http://arxiv.org/pdf/1408.1980 arXiv 1408.1980]]
  * @see [[edu.cmu.cs.ls.keymaerax.core.Provable.apply(edu.cmu.cs.ls.keymaerax.core.UniformSubstitution)]]
  * @example Uniform substitution can be applied to a formula
  * {{{
  *   val p = Function("p", None, Real, Bool)
  *   val x = Variable("x", None, Real)
  *   // p(x) <-> ! ! p(- - x)
  *   val prem = Equiv(PredOf(p, x), Not(Not(PredOf(p, Neg(Neg(x))))))
  *   val s = USubst(Seq(SubstitutionPair(PredOf(p, DotTerm),
  *       GreaterEqual(Power(DotTerm, Number(5)), Number(0)))))
  *   // x^5>=0 <-> !(!((-(-x))^5>=0))
  *   println(s(prem))
  * }}}
  * @example Uniform substitutions can be applied via the uniform substitution proof rule to a sequent:
  * {{{
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
  * }}}
  * @example Uniform substitutions also work for substituting hybrid programs
  * {{{
  *   val p = Function("p", None, Real, Bool)
  *   val x = Variable("x", None, Real)
  *   val a = ProgramConst("a")
  *   // [a]p(x) <-> [a](p(x)&true)
  *   val prem = Equiv(Box(a, PredOf(p, x)), Box(a, And(PredOf(p, x), True)))
  *   val s = USubst(Seq(SubstitutionPair(PredOf(p, DotTerm), GreaterEqual(DotTerm, Number(2))),
  *     SubstitutionPair(a, ODESystem(AtomicODE(DifferentialSymbol(x), Number(5)), True))))
  *   // "[x'=5;]x>=2 <-> [x'=5;](x>=2&true)".asFormula
  *   println(s(prem))
  * }}}
  * @example Uniform substitution rule also works when substitution hybrid programs
  * {{{
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
  * }}}
  */
final case class USubst(subsDefsInput: immutable.Seq[SubstitutionPair]) extends (Expression => Expression) {
  /** automatically filter out identity substitution no-ops, which can happen by systematic constructions such as unification */
  private[this] val subsDefs: immutable.Seq[SubstitutionPair] = subsDefsInput.filter(p => p.what != p.repl)

  insist(noException(dataStructureInvariant), "unique left-hand sides in substitutees " + this)

  /** unique left hand sides in subsDefs */
  private def dataStructureInvariant: Unit = {
    // check that we never replace n by something and then again replacing the same n by something
    val lefts = subsDefsInput.map(_.what).toList
    insist(lefts.distinct.size == lefts.size, "conflict: no duplicate substitutions for the same substitutee " + subsDefsInput)
    // check that we never replace p(x) by something and also p(t) by something
    val lambdaNames = matchKeys
    insist(lambdaNames.distinct.size == lambdaNames.size, "conflict: no duplicate substitutions for the same substitutee (modulo renaming) " + this)
  }

  override def toString: String = "USubst{" + subsDefs.mkString(", ") + "}"


  /**
    * The (new) free variables that this substitution introduces (without DotTerm/DotFormula arguments).
    * That is the (new) free variables introduced by this substitution, i.e.
    * free variables of all repl that are not bound as arguments in what.
    * @return union of the freeVars of all our substitution pairs.
    */
  lazy val freeVars: SetLattice[Variable] = {
    subsDefs.foldLeft(bottom[Variable])((a,b) => a ++ b.freeVars)
  } ensuring(r => r == subsDefs.map(_.freeVars).
    foldLeft(bottom[Variable])((a,b) => a++b), "free variables identical, whether computed with map or with fold")

  /**
    * The signature of the replacement introduced by this substitution.
    * @return union of the freeVars of all our substitution pairs.
    */
  lazy val signature: immutable.Set[NamedSymbol] = {
    subsDefs.foldLeft(Set.empty[NamedSymbol])((a,b) => a ++ b.signature)
  } ensuring(r => r == subsDefs.map(_.signature).
    foldLeft(Set.empty[NamedSymbol])((a,b) => a++b), "signature identical, whether computed with map or with fold")

  /**
    * The key characteristic expression constituents that this Substitution is matching on.
    * @return union of the matchKeys of all our substitution pairs.
    */
  private[core] lazy val matchKeys: immutable.List[NamedSymbol] = {
    subsDefs.foldLeft(immutable.List[NamedSymbol]())((a,b) => a ++ immutable.List(b.matchKey))
  }


  // apply calls usubst, augmenting with contract and exception context handling

  def apply(e: Expression): Expression = e match {
    case t: Term => apply(t)
    case f: Formula => apply(f)
    //@note This case happens for standalone uniform substitutions on differential programs such as x'=f() or c as they come up in unification for example.
    case p: DifferentialProgram => apply(p)
    case p: Program => apply(p)
  }

  //@note could define a direct composition implementation for fast compositions of USubst, but not used.

  /** apply this uniform substitution everywhere in a term */
  //@todo could optimize empty subsDefs to be identity right away if that happens often (unlikely)
  def apply(t: Term): Term = {try usubst(t) catch {case ex: ProverException => throw ex.inContext(t.prettyString)}
  } ensuring(r => matchKeys.toSet.intersect(StaticSemantics.signature(r)--signature).isEmpty,
    "Uniform Substitution substituted all occurrences (except when reintroduced by substitution) " + this + "\non" + t + "\ngave " + usubst(t))
  /** apply this uniform substitution everywhere in a formula */
  def apply(f: Formula): Formula = {try usubst(f) catch {case ex: ProverException => throw ex.inContext(f.prettyString)}
  } ensuring(r => matchKeys.toSet.intersect(StaticSemantics.signature(r)--signature).isEmpty,
    "Uniform Substitution substituted all occurrences (except when reintroduced by substitution) " + this + "\non" + f + "\ngave " + usubst(f))
  /** apply this uniform substitution everywhere in a program */
  def apply(p: Program): Program = {try usubst(p) catch {case ex: ProverException => throw ex.inContext(p.prettyString)}
  } ensuring(r => matchKeys.toSet.intersect(StaticSemantics.signature(r)--signature).isEmpty,
    "Uniform Substitution substituted all occurrences (except when reintroduced by substitution) " + this + "\non" + p + "\ngave " + usubst(p))
  /** apply this uniform substitution everywhere in a differential program */
  def apply(p: DifferentialProgram): DifferentialProgram = {try usubst(p).asInstanceOf[DifferentialProgram] catch {case ex: ProverException => throw ex.inContext(p.prettyString)}
  } ensuring(r => matchKeys.toSet.intersect(StaticSemantics.signature(r)--signature).isEmpty,
    "Uniform Substitution substituted all occurrences (except when reintroduced by substitution) " + this + "\non" + p + "\ngave " + usubst(p))

  /**
    * Apply uniform substitution everywhere in the sequent.
    */
  def apply(s: Sequent): Sequent = try {
    //@note mapping apply instead of the equivalent usubst makes sure the exceptions are augmented and the ensuring contracts checked.
    Sequent(s.ante.map(apply), s.succ.map(apply))
  } catch { case ex: ProverException => throw ex.inContext(s.toString) }

  /**
    * Apply uniform substitution to a Provable (convenience method).
    * @return `pr(this)`
    * @note Convenience method not used in the core.
    * @see [[Provable.apply(USubst)]]
    */
  def apply(pr: Provable): Provable = pr.apply(this)


  /** Union of uniform substitutions, i.e., both replacement lists merged.
    * @note Convenience method not used in the core, but used for stapling uniform substitutions together during unification etc.
    */
  def ++(other: USubst): USubst = USubst((this.subsDefsInput ++ other.subsDefsInput).distinct)


  /**
    * Whether this substitution matches to replace the given expression e,
    * because there is a substitution pair that matches e.
    */
  @inline private def matchHead(e: ApplicationOf): Boolean =
    subsDefs.exists(sp => sp.what.isInstanceOf[ApplicationOf] && sp.sameHead(e))

  // implementation of uniform substitution application
      
  /** uniform substitution on terms */
  private def usubst(term: Term): Term = {
    term match {
      // uniform substitution base cases
      case x: Variable => assert(!subsDefs.exists(_.what == x), "Substitution of variables not supported: " + x)
        x
//      case xp: DifferentialSymbol => assert(!subsDefs.exists(_.what == xp), "Substitution of differential symbols not supported: " + xp)
//        xp
      case app@FuncOf(of, theta) if matchHead(app) =>
        val subs = uniqueElementOf[SubstitutionPair](subsDefs, sp => sp.what.isInstanceOf[FuncOf] && sp.sameHead(app))
        val FuncOf(wf, wArg) = subs.what
        assert(wf == of, "match on same function heads")
        assert(wArg.isInstanceOf[DotTerm] || wArg == Nothing)
        // unofficial substitution for Nothing (no effect) and Anything in analogy to substitution for DotTerm
        //@note Uniform substitution of the argument placeholder applied to the replacement subs.repl for the shape subs.what
        USubst(SubstitutionPair(wArg, usubst(theta)) :: Nil).usubst(subs.repl.asInstanceOf[Term])
      case app@FuncOf(g:Function, theta) if !matchHead(app) => FuncOf(g, usubst(theta))
      case Nothing =>
        assert(!subsDefs.exists(sp => sp.what == Nothing /*&& sp.repl != Nothing*/), "can replace Nothing only by Nothing, and nothing else");
        Nothing
      case DotTerm(_) if  subsDefs.exists(_.what.isInstanceOf[DotTerm]) =>
        subsDefs.find(_.what.isInstanceOf[DotTerm]).get.repl.asInstanceOf[Term]
      case DotTerm(_) if !subsDefs.exists(_.what.isInstanceOf[DotTerm]) => term
      case n: Number => n
      //@note except for Differential, the following cases are equivalent to f.reapply but are left explicit to enforce revisiting this case when data structure changes.
      // case f:BinaryCompositeTerm => f.reapply(usubst(f.left), usubst(f.right))
      // homomorphic cases
      case Neg(e) => Neg(usubst(e))
      case Plus(l, r)   => Plus(usubst(l),   usubst(r))
      case Minus(l, r)  => Minus(usubst(l),  usubst(r))
      case Times(l, r)  => Times(usubst(l),  usubst(r))
      case Divide(l, r) => Divide(usubst(l), usubst(r))
      case Power(l, r)  => Power(usubst(l),  usubst(r))
      case der@Differential(e) => requireAdmissible(allVars, e, term)
        Differential(usubst(e))
      // unofficial
      case Pair(l, r) => Pair(usubst(l), usubst(r))
      case f: UnitFunctional =>
        subsDefs.find(sp => sp.what==f).getOrElse(SubstitutionPair(f,f)).repl.asInstanceOf[Term]
    }
  } ensuring(r => r.kind==term.kind && r.sort==term.sort, "Uniform Substitution leads to same kind and same sort " + term)

  /** uniform substitution on formulas */
  private def usubst(formula: Formula): Formula = {
    formula match {
      case p: UnitPredicational =>
        subsDefs.find(sp => sp.what==p).getOrElse(SubstitutionPair(p,p)).repl.asInstanceOf[Formula]
      case app@PredOf(op, theta) if matchHead(app) =>
        val subs = uniqueElementOf[SubstitutionPair](subsDefs, sp => sp.what.isInstanceOf[PredOf] && sp.sameHead(app))
        val PredOf(wp, wArg) = subs.what
        assert(wp == op, "match only if same head")
        assert(wArg.isInstanceOf[DotTerm] || wArg == Nothing)
        // unofficial substitution for Nothing (no effect) and Anything in analogy to substitution for DotTerm
        //@note Uniform substitution of the argument placeholder applied to the replacement subs.repl for the shape subs.what
        USubst(SubstitutionPair(wArg, usubst(theta)) :: Nil).usubst(subs.repl.asInstanceOf[Formula])
      case app@PredOf(q, theta) if !matchHead(app) => PredOf(q, usubst(theta))
      case app@PredicationalOf(op, fml) if matchHead(app) =>
        requireAdmissible(allVars, fml, formula)
        val subs = uniqueElementOf[SubstitutionPair](subsDefs, sp => sp.what.isInstanceOf[PredicationalOf] && sp.sameHead(app))
        val PredicationalOf(wp, wArg) = subs.what
        assert(wp == op, "match only if same head")
        assert(wArg == DotFormula)
        USubst(SubstitutionPair(wArg, usubst(fml)) :: Nil).usubst(subs.repl.asInstanceOf[Formula])
      case app@PredicationalOf(q, fml) if !matchHead(app) =>
        requireAdmissible(allVars, fml, formula)
        PredicationalOf(q, usubst(fml))
      case DotFormula if  subsDefs.exists(_.what == DotFormula) =>
        subsDefs.find(_.what == DotFormula).get.repl.asInstanceOf[Formula]
      case DotFormula if !subsDefs.exists(_.what == DotFormula) => DotFormula
      case True | False => formula

      //@note except for DifferentialFormula, the following cases are equivalent to f.reapply but are left explicit to enforce revisiting this case when data structure changes.
      // case f:BinaryCompositeTerm => f.reapply(usubst(f.left), usubst(f.right))

      // pseudo-homomorphic cases
      case Equal(l, r)        => Equal(usubst(l), usubst(r))
      case NotEqual(l, r)     => NotEqual(usubst(l), usubst(r))
      case GreaterEqual(l, r) => GreaterEqual(usubst(l), usubst(r))
      case Greater(l, r)      => Greater(usubst(l), usubst(r))
      case LessEqual(l, r)    => LessEqual(usubst(l), usubst(r))
      case Less(l, r)         => Less(usubst(l), usubst(r))

      // homomorphic cases
      case Not(g)      => Not(usubst(g))
      case And(l, r)   => And(usubst(l), usubst(r))
      case Or(l, r)    => Or(usubst(l), usubst(r))
      case Imply(l, r) => Imply(usubst(l), usubst(r))
      case Equiv(l, r) => Equiv(usubst(l), usubst(r))

      // NOTE DifferentialFormula in analogy to Differential
      case der@DifferentialFormula(g) => requireAdmissible(allVars, g, formula)
        DifferentialFormula(usubst(g))

      // binding cases add bound variables to u
      case Forall(vars, g) => requireAdmissible(SetLattice(vars), g, formula)
        Forall(vars, usubst(g))
      case Exists(vars, g) => requireAdmissible(SetLattice(vars), g, formula)
        Exists(vars, usubst(g))

      // Note could optimize speed by avoiding duplicate computation unless Scalac knows about CSE
      case Box(p, g) => requireAdmissible(StaticSemantics(usubst(p)).bv, g, formula)
        Box(usubst(p), usubst(g))
      case Diamond(p, g) => requireAdmissible(StaticSemantics(usubst(p)).bv, g, formula)
        Diamond(usubst(p), usubst(g))
    }
  } ensuring(r => r.kind==formula.kind && r.sort==formula.sort, "Uniform Substitution leads to same kind and same sort " + formula)

  /** uniform substitution on programs */
  private def usubst(program: Program): Program = {
    program match {
      case a: ProgramConst if subsDefs.exists(_.what == a) =>
        subsDefs.find(_.what == a).get.repl.asInstanceOf[Program]
      case a: ProgramConst if !subsDefs.exists(_.what == a) => a
      case Assign(x, e)      => Assign(x, usubst(e))
      case a: AssignAny      => a
      case Test(f)           => Test(usubst(f))
      case ODESystem(ode, h) =>
        //@note requireAdmissible(StaticSemantics(usubstODE(ode, SetLattice.bottom)).bv, ...) would be sound just more permissive
        requireAdmissible(StaticSemantics(ode).bv, h, program)
        ODESystem(usubst(ode), usubst(h))
      case Choice(a, b)      => Choice(usubst(a), usubst(b))
      case Compose(a, b)     => requireAdmissible(StaticSemantics(usubst(a)).bv, b, program)
        Compose(usubst(a), usubst(b))
      case Loop(a)           => requireAdmissible(StaticSemantics(usubst(a)).bv, a, program)
        Loop(usubst(a))
      case Dual(a)           => Dual(usubst(a))
    }
  } ensuring(r => r.kind==program.kind && r.sort==program.sort, "Uniform Substitution leads to same kind and same sort " + program)

  /** uniform substitution on differential programs */
  private def usubst(ode: DifferentialProgram): DifferentialProgram = {
    //@note This case is a mixture of AtomicODE and ProgramConst. Only admissibility wrt BV still bound in the result (after substitution of DifferentialProgramConst) but admissible within the whole system simultaneously.
    //@note Conceptually easiest (albeit suboptimally efficient): pre-substitute without taboos to determine BV, then check admissibility during the proper substitution w.r.t. those BV as in other cases.
    requireAdmissible(StaticSemantics(usubstODE(ode, SetLattice.bottom)).bv, ode, ode)
    //@note the requires checking within usubstODE(ode, odeBV) will be redundant but locally the right thing to do.
    //@note usubstODE(ode, StaticSemantics(usubstODE(ode, SetLattice.bottom)).bv) would be sound just more permissive
    usubstODE(ode, StaticSemantics(ode).bv)
  } ensuring(r => r.kind==ode.kind && r.sort==ode.sort, "Uniform Substitution leads to same kind and same sort " + ode)

  /**
    * uniform substitutions on differential programs
    * @param odeBV the bound variables of the whole ODESystem within which ode occurs, so all odeBV are taboo during the substitution.
    */
  private def usubstODE(ode: DifferentialProgram, odeBV: SetLattice[Variable]): DifferentialProgram = {
    ode match {
      case AtomicODE(xp: DifferentialSymbol, e) => requireAdmissible(odeBV, e, ode)
        AtomicODE(xp, usubst(e))
      case c: DifferentialProgramConst if subsDefs.exists(_.what == c) =>
        subsDefs.find(_.what == c).get.repl.asInstanceOf[DifferentialProgram]
      case c: DifferentialProgramConst if !subsDefs.exists(_.what == c) => c
      // homomorphic cases
      case DifferentialProduct(a, b) => DifferentialProduct(usubstODE(a, odeBV), usubstODE(b, odeBV))
    }
  } ensuring(r => r.kind==ode.kind && r.sort==ode.sort, "Uniform Substitution leads to same kind and same sort " + ode)


  // admissibility

  /**
    * Is this uniform substitution U-admissible for expression e?
    */
  @inline private def admissible(U: SetLattice[Variable], e: Expression): Boolean = admissible(U, StaticSemantics.signature(e))

  /**
    * Require that this uniform substitution is U-admissible for expression e, and
    * raise informative exception if not.
    */
  @inline private def requireAdmissible(U: SetLattice[Variable], e: Expression, context: Expression): Unit =
    if (!admissible(U, e))
      throw new SubstitutionClashException(toString, U.prettyString, e.prettyString, context.prettyString, clashSet(U, e).prettyString, "")

  /**
    * check whether this substitution is U-admissible for an expression with the given occurrences of functions/predicates symbols.
    * @param U taboo list of variables
    * @param occurrences the function and predicate symbols occurring in the expression of interest.
    * @see Definition 19 in Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
    * @see arXiv:1503.01981 Definition 12.
    */
  @inline private def admissible(U: SetLattice[Variable], occurrences: immutable.Set[NamedSymbol]): Boolean =
    // U-admissible iff FV(restrict this to occurrences) /\ U = empty
    clashSet(U, occurrences).isEmpty
    // this + " is " + U + "-admissible iff restriction " + projection(occurrences) + " to occurring symbols " + occurrences + " has no free variables " + projection(occurrences).freeVars + " of " + U)

  /**
    * Projects / restricts a substitution to only those that affect the symbols listed in occurrences.
    * @see Definition 19 in Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
    * @see arXiv:1503.01981 Definition 12.
    */
  @inline private def projection(affected: immutable.Set[NamedSymbol]): USubst = new USubst(
    subsDefs.filter(sigma => affected.contains(sigma.matchKey))
  )

  /**
    * Compute the set of all symbols for which this substitution clashes because it is not U-admissible
    * for the given expression.
    * @param U taboo list of variables
    * @param e the expression of interest.
    * @return FV(restrict this to occurrences) /\ U
    * @see Definition 19 in Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
    * @see arXiv:1503.01981 Definition 12.
    * @note not used often
    */
  @inline private def clashSet(U: SetLattice[Variable], e: Expression): SetLattice[Variable] =
    clashSet(U, StaticSemantics.signature(e))

  /**
    * Compute the set of all symbols for which this substitution clashes because it is not U-admissible
    * for an expression with the given occurrences of functions/predicates symbols.
    * @param U taboo list of variables
    * @param occurrences the function and predicate symbols occurring in the expression of interest.
    * @return FV(restrict this to occurrences) /\ U
    * @see Definition 19 in Andre Platzer. [[http://dx.doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
    * @see arXiv:1503.01981 Definition 12.
    */
  @inline private def clashSet(U: SetLattice[Variable], occurrences: immutable.Set[NamedSymbol]): SetLattice[Variable] =
    projection(occurrences).freeVars.intersect(U)

  /**
    * Get the unique element in c to which pred applies.
    * Protests if that element is not unique because pred applies to more than one element in c or if there is none.
    */
  @inline private def uniqueElementOf[E](c: Iterable[E], pred: E => Boolean): E = {
    //require(c.count(pred) == 1, "unique element expected in " + c.mkString)
    val matching = c.filter(pred)
    require(matching.tail.isEmpty, "unique elemented expected in " + c.mkString)
    matching.head
  }
}
