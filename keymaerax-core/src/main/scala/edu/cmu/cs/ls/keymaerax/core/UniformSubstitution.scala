/**
* Copyright (c) Carnegie Mellon University. CONFIDENTIAL
* See LICENSE.txt for the conditions of this license.
*/
/**
 * Uniform Substitution for KeYmaera
 * @author aplatzer
 * @author smitsch
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @note Code Review: 2015-05-01
 */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable

import SetLattice.bottom
import SetLattice.topVarsDiffVars


/**
 * Representation of a substitution replacing what with repl uniformly.
 *
 * @param what the expression to be replaced. what can have one of the following forms:
 *          - DotTerm
 *          - Anything
 *          - ApplyPredicate(p:Function, DotTerm/Nothing/Anything)
 *          - Apply(f:Function, DotTerm/Nothing/Anything)
 *          - ProgramConstant/DifferentialProgramConstant
 *          - Derivative(...)
 *          - ApplyPredicational(p:Function, DotFormula)
 *          - DotFormula
 * @param repl the expression to be used in place of what
 */
final case class SubstitutionPair (what: Expression, repl: Expression) {
  require(what.kind == repl.kind,
    "substitution to same kind of expression (terms for terms, formulas for formulas, programs for programs) " + this + " substitutes " + what.kind + " ~> " + repl.kind)
  require(what.sort == repl.sort, "Sorts have to match in substitution pairs: " + what.sort + " != " + repl.sort)
  assert(what match {
    case _: Term => repl.isInstanceOf[Term]
    case _: Formula => repl.isInstanceOf[Formula]
    case _: Program => repl.isInstanceOf[Program]
  }, "(redundant test) substitution to same kind of expression (terms for terms, formulas for formulas, programs for programs) " + this + " substitutes " + what.kind + " ~> " + repl.kind)
  matchKey // matchKey will throw exception if requirement("Substitutable expression required, found " + what + " in " + this) failed

  /**
   * The (new) free variables that this substitution introduces (without DotTerm/DotFormula arguments).
   * That is the (new) free variables introduced by this substitution, i.e. free variables of repl that are not bound as arguments in what.
   * @return essentially freeVars(repl) except for special handling of Anything arguments.
   */
  def freeVars: SetLattice[NamedSymbol] = repl match {
    case replt: Term => what match {
      case FuncOf(f: Function, Anything) => bottom[NamedSymbol] // Anything locally binds all variables
      case FuncOf(f: Function, DotTerm) =>
        assert(!StaticSemantics.freeVars(replt).contains(DotTerm)/* || StaticSemantics(replt).isTop*/, "DotTerm is no variable")
        assert(!(StaticSemantics.freeVars(replt) -- Set(DotTerm)).contains(DotTerm), "COMPLETENESS WARNING: removal of DotTerm from freeVars unsuccessful " + (StaticSemantics(replt) -- Set(DotTerm)) + " leading to unnecessary clashes")
        assert(StaticSemantics.freeVars(replt) -- Set(DotTerm) == StaticSemantics.freeVars(replt), "DotTerm is no free variable, so removing it won't change") // since DotTerm shouldn't be in, could be changed to StaticSemantics(replt) if lattice would know that.
        StaticSemantics.freeVars(repl)
      case _: Term => StaticSemantics.freeVars(repl)
    }
    case replf: Formula => what match {
      case PredOf(p: Function, Anything) => bottom[NamedSymbol] // Anything locally binds all variables
      case PredOf(p: Function, DotTerm) =>
        assert(!StaticSemantics.freeVars(replf).contains(DotTerm) /*|| StaticSemantics(replf).fv.isTop*/, "DotTerm is no variable")
        assert(!(StaticSemantics.freeVars(replf) -- Set(DotTerm)).contains(DotTerm), "COMPLETENESS WARNING: removal of DotTerm from freeVars unsuccessful " + (StaticSemantics(replf).fv -- Set(DotTerm)) + " leading to unnecessary clashes")
        assert(StaticSemantics.freeVars(replf) -- Set(DotTerm) == StaticSemantics.freeVars(replf), "DotTerm is no free variable, so removing it won't change") // since DotTerm shouldn't be in, could be changed to StaticSemantics(replt) if lattice would know that.
        StaticSemantics.freeVars(repl)
      // predicationals are not function nor predicate symbols
      case PredicationalOf(ctx: Function, DotFormula) => bottom
      // DotFormula is a nullary Predicational
      case DotFormula => bottom
      case _: Formula => StaticSemantics.freeVars(repl)
    }
    case replp: Program => what match {
      case _: ProgramConst | _: DifferentialProgramConst => bottom[NamedSymbol] // program constants are always admissible, since their meaning doesn't depend on state
      case _ => throw new IllegalStateException("Disallowed substitution shape " + this)
    }
  }

  /**
   * The signature of the replacement introduced by this substitution.
   * @note DotTerm and DotFormula arguments don't literally occur if bound by p(DotTerm) ~> DotTerm>5
   */
  def signature: immutable.Set[NamedSymbol] = repl match {
    case replt: Term => what match {
      case FuncOf(f: Function, DotTerm) =>
        StaticSemantics.signature(repl) -- immutable.Set(DotTerm)
      case _: Term => StaticSemantics.signature(repl)
    }
    case replf: Formula => what match {
      case PredOf(p: Function, DotTerm) =>
        StaticSemantics.signature(repl) -- immutable.Set(DotTerm)
      case PredicationalOf(ctx: Function, DotFormula) =>
        StaticSemantics.signature(repl) -- immutable.Set(DotFormula)
      case _: Formula => StaticSemantics.signature(repl)
    }
    case replp: Program => StaticSemantics.signature(repl)
  }

  /**
   * The key characteristic expression constituent that this SubstitutionPair is matching on.
   * @return only the lead / key part that this SubstitutionPair is matching on,
   *         which may not be its head.
   */
  private[core] def matchKey: NamedSymbol = what match {
    case DotTerm => DotTerm
    case FuncOf(f: Function, DotTerm | Nothing | Anything) => f
    case PredOf(p: Function, DotTerm | Nothing | Anything) => p
    case Anything => Anything
    case Nothing => assert(repl == Nothing, "can replace Nothing only by Nothing, and nothing else"); Nothing // it makes no sense to substitute Nothing
    case a: DifferentialProgramConst => a
    case a: ProgramConst => a
    case DotFormula => DotFormula
    case PredicationalOf(p: Function, DotFormula) => p
    case _ => throw new IllegalArgumentException("Nonsubstitutable expression " + this)
  }

  /**
   * Check whether we match on the term other, i.e. both have the same head.
   */
  private[core] def sameHead(other: Expression): Boolean = what match {
    case FuncOf(lf, arg) =>
      assert(arg match { case DotTerm | Anything | Nothing => true case _ => false }, "Only DotTerm/Anything/Nothing allowed as argument")
      other match { case FuncOf(rf, _) => lf == rf case _ => false }
    case PredOf(lf, arg) =>
      assert(arg match { case DotTerm | Anything | Nothing => true case _ => false }, "Only DotTerm/Anything/Nothing allowed as argument")
      other match { case PredOf(rf, _) => lf == rf case _ => false }
    case PredicationalOf(lf, arg) =>
      assert(arg match { case DotFormula => true case _ => false }, "Only DotFormula allowed as argument")
      other match { case PredicationalOf(rf, _) => lf == rf case _ => false }
    case _ => assert(false, "sameHead only used for ApplicationOf"); false
  }

  override def toString: String = "(" + what.prettyString() + "~>" + repl.prettyString() + ")"
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
 * Main ingredient of [[edu.cmu.cs.ls.keymaerax.core.UniformSubstitutionRule]]
 * and [[edu.cmu.cs.ls.keymaerax.core.AxiomaticRule]]
 * @author aplatzer
 * @see Andre Platzer. [[http://www.cs.cmu.edu/~aplatzer/pub/usubst.pdf A uniform substitution calculus for differential dynamic logic]].  In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, LNCS. Springer, 2015.
 * @see Andre Platzer. [[http://arxiv.org/pdf/1503.01981.pdf A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981]], 2015.
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
 *     Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
 *       Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
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
 *    Sequent(Seq(), IndexedSeq(), IndexedSeq(prem)))(
 *      Sequent(Seq(), IndexedSeq(), IndexedSeq(conc)))
 *   // results in: [x'=5;]x>=2 <-> [x'=5;](x>=2&true)
 *   println(next)
 * }}}
 * @see [[edu.cmu.cs.ls.keymaerax.core.USubst]]
 */
final case class USubst(subsDefsInput: immutable.Seq[SubstitutionPair]) extends (Expression => Expression) {
  /** automatically filter out identity substitution no-ops */
  val subsDefs: immutable.Seq[SubstitutionPair] = subsDefsInput.filter(p => p.what != p.repl)

  applicable()
  /** unique left hand sides in subsDefs */
  private def applicable(): Unit = {
    // check that we never replace n by something and then again replacing the same n by something
    val lefts = subsDefsInput.map(_.what).toList
    require(lefts.distinct.size == lefts.size, "no duplicate substitutions with same substitutees " + subsDefsInput)
    // check that we never replace p(x) by something and also p(t) by something
    val lambdaNames = matchKeys
    require(lambdaNames.distinct.size == lambdaNames.size, "no duplicate substitutions with same substitutee modulo alpha-renaming of lambda terms " + this)
  }

  private def log(msg: =>String): Unit = {}  //= println(msg)

  override def toString: String = "USubst{" + subsDefs.mkString(", ") + "}"

  // apply calls usubst, augmenting with contract and exception context handling

  def apply(e: Expression): Expression = e match {
    case t: Term => apply(t)
    case f: Formula => apply(f)
    case p: Program => apply(p)
  }

  //@note could define a direct composition implementation for fast compositions of USubst, but not used.

  /** apply this uniform substitution everywhere in a term */
  def apply(t: Term): Term = {try usubst(t) catch {case ex: ProverException => throw ex.inContext(t.prettyString())}
  } ensuring(r => matchKeys.toSet.intersect(StaticSemantics.signature(r)--signature).isEmpty,
    "Uniform Substitution substituted all occurrences (except when reintroduced by substitution) " + this + "\non" + t + "\ngave " + usubst(t))
  /** apply this uniform substitution everywhere in a formula */
  def apply(f: Formula): Formula = {try usubst(f) catch {case ex: ProverException => throw ex.inContext(f.prettyString())}
  } ensuring(r => matchKeys.toSet.intersect(StaticSemantics.signature(r)--signature).isEmpty,
    "Uniform Substitution substituted all occurrences (except when reintroduced by substitution) " + this + "\non" + f + "\ngave " + usubst(f))
  /** apply this uniform substitution everywhere in a program */
  def apply(p: Program): Program = {try usubst(p) catch {case ex: ProverException => throw ex.inContext(p.prettyString())}
  } ensuring(r => matchKeys.toSet.intersect(StaticSemantics.signature(r)--signature).isEmpty,
    "Uniform Substitution substituted all occurrences (except when reintroduced by substitution) " + this + "\non" + p + "\ngave " + usubst(p))

  /**
   * Apply uniform substitution everywhere in the sequent.
   */
  def apply(s: Sequent): Sequent = {
    try {
      Sequent(s.pref, s.ante.map(usubst), s.succ.map(usubst))
    } catch {
      case ex: ProverException => throw ex.inContext(s.toString)
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(toString, "undef", "undef", s.toString, "undef", ex.getMessage).initCause(ex)
    }
  }

  /**
   * The (new) free variables that this substitution introduces (without DotTerm/DotFormula arguments).
   * That is the (new) free variables introduced by this substitution, i.e.
   * free variables of all repl that are not bound as arguments in what.
   * @return union of the freeVars of all our substitution pairs.
   */
  def freeVars: SetLattice[NamedSymbol] = {
    subsDefs.foldLeft(bottom[NamedSymbol])((a,b)=>a ++ b.freeVars)
  } ensuring(r => r == subsDefs.map(_.freeVars).
      foldLeft(bottom[NamedSymbol])((a,b)=>a++b), "free variables identical, whether computed with map or with fold")

  /**
   * The signature of the replacement introduced by this substitution.
   * @return union of the freeVars of all our substitution pairs.
   */
  def signature: immutable.Set[NamedSymbol] = {
    subsDefs.foldLeft(Set.empty[NamedSymbol])((a,b)=>a ++ b.signature)
  } ensuring(r => r == subsDefs.map(_.signature).
    foldLeft(Set.empty[NamedSymbol])((a,b)=>a++b), "signature identical, whether computed with map or with fold")

  /**
   * The key characteristic expression constituents that this Substitution is matching on.
   * @return union of the matchKeys of all our substitution pairs.
   */
  def matchKeys: immutable.List[NamedSymbol] = {
    subsDefs.foldLeft(immutable.List[NamedSymbol]())((a,b)=>a ++ immutable.List(b.matchKey))
  }

  /**
   * Whether this substitution matches to replace the given expression e,
   * because there is a substitution pair that matches e.
   */
  private def matchHead(e: Expression): Boolean = subsDefs.filter(_.what.isInstanceOf[ApplicationOf]).exists(sp => sp.sameHead(e))


  // implementation of uniform substitution application
      
  /** uniform substitution on terms */
  private[core] def usubst(term: Term): Term = {
    try {
      term match {
        // uniform substitution base cases
        case x: Variable => assert(!subsDefs.exists(_.what == x), "Substitution of variables not supported: " + x)
          x
        case xp: DifferentialSymbol => assert(!subsDefs.exists(_.what == xp), "Substitution of differential symbols not supported: " + xp)
          xp
        case app@FuncOf(of, theta) if matchHead(app) =>
          val subs = uniqueElementOf[SubstitutionPair](subsDefs, sp => sp.what.isInstanceOf[FuncOf] && sp.sameHead(app))
          val FuncOf(rf, rArg) = subs.what
          assert(rf == of, "match on same function heads")
          assert(rArg == DotTerm || rArg == Nothing || rArg == Anything)
          // unofficial substitution for Nothing (no effect) and Anything in analogy to substitution for DotTerm
          USubst(SubstitutionPair(rArg, usubst(theta)) :: Nil).usubst(subs.repl.asInstanceOf[Term])
        case app@FuncOf(g:Function, theta) if !matchHead(app) => FuncOf(g, usubst(theta))
        case Anything =>
          assert(!subsDefs.exists(_.what == Anything), "Substitution of anything not supported " + this)
          Anything
        case Nothing =>
          assert(!subsDefs.exists(sp => sp.what == Nothing /*&& sp.repl != Nothing*/), "can replace Nothing only by Nothing, and nothing else");
          Nothing
        case DotTerm if  subsDefs.exists(_.what == DotTerm) =>
          subsDefs.find(_.what == DotTerm).get.repl.asInstanceOf[Term]
        case DotTerm if !subsDefs.exists(_.what == DotTerm) => DotTerm
        case n: Number => n
         // homomorphic cases
        case Neg(e) => Neg(usubst(e))
        case Plus(l, r)   => Plus(usubst(l),   usubst(r))
        case Minus(l, r)  => Minus(usubst(l),  usubst(r))
        case Times(l, r)  => Times(usubst(l),  usubst(r))
        case Divide(l, r) => Divide(usubst(l), usubst(r))
        case Power(l, r)  => Power(usubst(l),  usubst(r))
        case der@Differential(e) => requireAdmissible(topVarsDiffVars(), e, term)
          Differential(usubst(e))
        // unofficial
        case Pair(l, r) => Pair(usubst(l), usubst(r))  
      }
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(toString, "undef", "undef", term.prettyString(), "undef", ex.getMessage).initCause(ex)
        throw new ProverAssertionError("Assertion failed " + ex.getMessage() + "\nin " + toString + "\nin " + term.prettyString()).initCause(ex)
    }
  } ensuring(
    r => r.kind == term.kind && r.sort == term.sort, "Uniform Substitution leads to same kind and same sort " + term)

  /** uniform substitution on formulas */
  private[core] def usubst(formula: Formula): Formula = {
    log("Substituting " + formula.prettyString() + " using " + this)
    try {
      formula match {
        case app@PredOf(op, theta) if matchHead(app) =>
          val subs = uniqueElementOf[SubstitutionPair](subsDefs, sp => sp.what.isInstanceOf[PredOf] && sp.sameHead(app))
          val PredOf(rp, rArg) = subs.what
          assert(rp == op, "match only if same head")
          assert(rArg == DotTerm || rArg == Nothing || rArg == Anything)
          // unofficial substitution for Nothing (no effect) and Anything in analogy to substitution for DotTerm
          USubst(SubstitutionPair(rArg, usubst(theta)) :: Nil).usubst(subs.repl.asInstanceOf[Formula])
        case app@PredOf(q, theta) if !matchHead(app) => PredOf(q, usubst(theta))
        case app@PredicationalOf(op, fml) if matchHead(app) =>
          requireAdmissible(topVarsDiffVars[NamedSymbol](), fml, formula)
          val subs = uniqueElementOf[SubstitutionPair](subsDefs, sp => sp.what.isInstanceOf[PredicationalOf] && sp.sameHead(app))
          val PredicationalOf(rp, rArg) = subs.what
          assert(rp == op, "match only if same head")
          assert(rArg == DotFormula)
          USubst(SubstitutionPair(rArg, usubst(fml)) :: Nil).usubst(subs.repl.asInstanceOf[Formula])
        case app@PredicationalOf(q, fml) if !matchHead(app) =>
          requireAdmissible(topVarsDiffVars[NamedSymbol](), fml, formula)
          PredicationalOf(q, usubst(fml))
        case DotFormula if  subsDefs.exists(_.what == DotFormula) =>
          subsDefs.find(_.what == DotFormula).get.repl.asInstanceOf[Formula]
        case DotFormula if !subsDefs.exists(_.what == DotFormula) => DotFormula
        case True | False => formula

        case Equal(l, r)        => Equal(usubst(l), usubst(r))
        case NotEqual(l, r)     => NotEqual(usubst(l), usubst(r))
        case GreaterEqual(l, r) => GreaterEqual(usubst(l), usubst(r))
        case Greater(l, r)      => Greater(usubst(l), usubst(r))
        case LessEqual(l, r)    => LessEqual(usubst(l), usubst(r))
        case Less(l, r)         => Less(usubst(l), usubst(r))

        // homomorphic cases
        case Not(g) => Not(usubst(g))
        case And(l, r)   => And(usubst(l), usubst(r))
        case Or(l, r)    => Or(usubst(l), usubst(r))
        case Imply(l, r) => Imply(usubst(l), usubst(r))
        case Equiv(l, r) => Equiv(usubst(l), usubst(r))

        // NOTE DifferentialFormula in analogy to Differential
        case der@DifferentialFormula(g) => requireAdmissible(topVarsDiffVars(), g, formula)
          DifferentialFormula(usubst(g))

        // binding cases add bound variables to u
        case Forall(vars, g) => requireAdmissible(SetLattice[NamedSymbol](vars), g, formula)
            Forall(vars, usubst(g))
        case Exists(vars, g) => requireAdmissible(SetLattice[NamedSymbol](vars), g, formula)
            Exists(vars, usubst(g))

        // Note could optimize speed by avoiding duplicate computation unless Scalac knows about CSE
        case Box(p, g) => requireAdmissible(StaticSemantics(usubst(p)).bv, g, formula)
            Box(usubst(p), usubst(g))
        case Diamond(p, g) => requireAdmissible(StaticSemantics(usubst(p)).bv, g, formula)
            Diamond(usubst(p), usubst(g))
      }
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(toString, "undef", "undef", formula.prettyString(), "undef", ex.getMessage).initCause(ex)
      case ex: AssertionError =>
        throw new ProverAssertionError("Assertion failed " + ex.getMessage() + "\nin " + toString + "\nin " + formula.prettyString()).initCause(ex)
    }
  } ensuring(
    r => r.kind == formula.kind && r.sort == formula.sort, "Uniform Substitution leads to same kind and same sort " + formula)

  /** uniform substitution on programs */
  private[core] def usubst(program: Program): Program = {
    try {
      program match {
        case a: ProgramConst if subsDefs.exists(_.what == a) =>
          subsDefs.find(_.what == a).get.repl.asInstanceOf[Program]
        case a: ProgramConst if !subsDefs.exists(_.what == a) => a
        case Assign(x, e) => Assign(x, usubst(e))
        case DiffAssign(xp, e) => DiffAssign(xp, usubst(e))
        case a: AssignAny => a
        case Test(f) => Test(usubst(f))
        //case IfThen(cond, thenT) => IfThen(usubst(cond), usubst(thenT))
        case ode: DifferentialProgram => requireAdmissible(StaticSemantics(ode).bv, ode, program)
          // require is redundant with the checks on NFContEvolve in usubst(ode, primed)
          usubstODE(ode, StaticSemantics(ode).bv)
        case Choice(a, b) => Choice(usubst(a), usubst(b))
        case Compose(a, b) => requireAdmissible(StaticSemantics(usubst(a)).bv, b, program)
          Compose(usubst(a), usubst(b))
        case Loop(a) => requireAdmissible(StaticSemantics(usubst(a)).bv, a, program)
          Loop(usubst(a))
      }
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(toString, "undef", "undef", program.prettyString(), "undef", ex.getMessage).initCause(ex)
      case ex: AssertionError =>
        throw new ProverAssertionError("Assertion failed " + ex.getMessage() + "\nin " + toString + "\nin " + program.prettyString()).initCause(ex)
    }
  } ensuring(
    r => r.kind == program.kind && r.sort == program.sort, "Uniform Substitution leads to same kind and same sort " + program)

  /** uniform substitutions on differential programs */
  private def usubstODE(ode: DifferentialProgram, odeBV: SetLattice[NamedSymbol]): DifferentialProgram = {
    ode match {
      case ODESystem(a, h) => requireAdmissible(odeBV, h, ode)
        // admissibility within ODE a will be checked recursively by usubstODE
        ODESystem(usubstODE(a, odeBV), usubst(h))
      case AtomicODE(xp: DifferentialSymbol, e) => requireAdmissible(odeBV, e, ode)
        AtomicODE(xp, usubst(e))
      case c: DifferentialProgramConst if subsDefs.exists(_.what == c) =>
        subsDefs.find(_.what == c).get.repl.asInstanceOf[DifferentialProgram]
      case c: DifferentialProgramConst if !subsDefs.exists(_.what == c) => c
      // homomorphic cases
      case DifferentialProduct(a, b) => DifferentialProduct(usubstODE(a, odeBV), usubstODE(b, odeBV))
    }
  } ensuring(
    r => r.kind == ode.kind && r.sort == ode.sort, "Uniform Substitution leads to same kind and same sort " + ode)

  // admissibility
  
  /**
   * Is this uniform substitution U-admissible for expression e?
   */
  private def admissible(U: SetLattice[NamedSymbol], e: Expression): Boolean = admissible(U, StaticSemantics.signature(e))

  /**
   * Require that this uniform substitution is U-admissible for expression e, and
   * raise informative exception if not.
   */
  private def requireAdmissible(U: SetLattice[NamedSymbol], e: Expression, context: Expression): Unit =
//    require(admissible(U, e),
//      "Substitution clash: " + this + " not " + U + "-admissible for " + e.prettyString() + " when substituting in " + context.prettyString())
    if (!admissible(U, e))
      throw new SubstitutionClashException(toString, U.prettyString, e.prettyString(), context.prettyString(), clashSet(U, e).prettyString, "")

  /**
   * check whether this substitution is U-admissible for an expression with the given occurrences of functions/predicates symbols.
   * @param U taboo list of variables
   * @param occurrences the function and predicate symbols occurring in the expression of interest.
   * @see arXiv:1503.01981 Definition 12.
   */
  private def admissible(U: SetLattice[NamedSymbol], occurrences: immutable.Set[NamedSymbol]): Boolean = {
      // if  no function symbol f in sigma with FV(sigma f(.)) /\ U != empty
      // and no predicate symbol p in sigma with FV(sigma p(.)) /\ U != empty
      // occurs in theta (or phi or alpha)
      def intersectsU(sigma: SubstitutionPair): Boolean =
        sigma.freeVars.intersect(U) != bottom

    subsDefs.filter(intersectsU).flatMap(sigma => StaticSemantics.signature(sigma.what)).forall(fn => !occurrences.contains(fn))
  } ensuring(r =>
    // U-admissible iff FV(restrict this to occurrences) /\ U = empty
    r == clashSet(U, occurrences).isEmpty,
    this + " is " + U + "-admissible iff restriction " + projection(occurrences) + " to occurring symbols " + occurrences + " has no free variables " + projection(occurrences).freeVars + " of " + U)

  /**
   * Projects / restricts a substitution to only those that affect the symbols listed in occurrences.
   * @see arXiv:1503.01981 Definition 12.
   */
  private def projection(affected: immutable.Set[NamedSymbol]): USubst = new USubst(
    subsDefs.filter(sigma => affected.contains(sigma.matchKey))
  )

  /**
   * Compute the set of all symbols for which this substitution clashes because it is not U-admissible
   * for the given expression.
   * @param U taboo list of variables
   * @param e the expression of interest.
   * @return FV(restrict this to occurrences) /\ U
   * @see arXiv:1503.01981 Definition 12.
   * @note not used often
   */
  private def clashSet(U: SetLattice[NamedSymbol], e: Expression): SetLattice[NamedSymbol] = clashSet(U, StaticSemantics.signature(e))

  /**
   * Compute the set of all symbols for which this substitution clashes because it is not U-admissible
   * for an expression with the given occurrences of functions/predicates symbols.
   * @param U taboo list of variables
   * @param occurrences the function and predicate symbols occurring in the expression of interest.
   * @return FV(restrict this to occurrences) /\ U
   * @see arXiv:1503.01981 Definition 12.
   */
  private def clashSet(U: SetLattice[NamedSymbol], occurrences: immutable.Set[NamedSymbol]): SetLattice[NamedSymbol] =
    projection(occurrences).freeVars.intersect(U)

  /**
   * Get the unique element in c to which pred applies.
   * Protests if that element is not unique because pred applies to more than one element in c or if there is none.
   */
  private def uniqueElementOf[E](c: Iterable[E], pred: E => Boolean): E = {
    require(c.count(pred) == 1, "unique element expected in " + c.mkString)
    c.filter(pred).head
  }
}
