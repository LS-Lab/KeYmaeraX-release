/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
  * Uniform Substitution for KeYmaera X
  * @author Andre Platzer
  * @see Andre Platzer. [[https://doi.org/10.1007/978-3-030-29436-6_25 Uniform substitution at one fell swoop]]. In Pascal Fontaine, editor, International Conference on Automated Deduction, CADE'19, Natal, Brazil, Proceedings, volume 11716 of LNCS, pp. 425-441. Springer, 2019.
  * @see Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 59(2), pp. 219-266, 2017.
  * @note Code Review: 2020-02-17
  */
package edu.cmu.cs.ls.keymaerax.core

import scala.collection.immutable
import StaticSemantics.boundVars
import SetLattice.allVars
import SetLattice.bottom

/**
  * A Uniform Substitution with its one-pass application mechanism.
  * A Uniform Substitution uniformly replaces all occurrences of a given predicate p(.) by a formula in (.).
  * It can also replace all occurrences of a function symbol f(.) by a term in (.)
  * and all occurrences of a predicational / quantifier symbols C(-) by a formula in (-)
  * and all occurrences of program constant symbol b by a hybrid program.
  *
  * This type implements the application of uniform substitutions to terms, formulas, programs, and sequents.
  *
  * @note Implements the one-pass version that checks admissibility on the fly and checking upon occurrence.
  *       Faster than the alternative [[USubstChurch]].
  * Main ingredient of prover core.
  * @note soundness-critical
  * @author Andre Platzer
  * Created by aplatzer on 2019-2-12.
  * @since 4.7
  * @see Andre Platzer. [[https://doi.org/10.1007/978-3-030-29436-6_25 Uniform substitution at one fell swoop]]. In Pascal Fontaine, editor, International Conference on Automated Deduction, CADE'19, Natal, Brazil, Proceedings, volume 11716 of LNCS, pp. 425-441. Springer, 2019.
  * @see [[edu.cmu.cs.ls.keymaerax.core.Provable.apply(subst:edu\.cmu\.cs\.ls\.keymaerax\.core\.USubstOne):edu\.cmu\.cs\.ls\.keymaerax\.core\.Provable*]]
  * @see [[USubstChurch]]
  */
final case class USubstOne(subsDefsInput: immutable.Seq[SubstitutionPair]) extends (Expression => Expression) {
  /** automatically filter out identity substitution no-ops, which can happen by systematic constructions such as unification */
  private/*[this]*/ val subsDefs: immutable.Seq[SubstitutionPair] = subsDefsInput.filter(p => p.what != p.repl)

  insist(noException(dataStructureInvariant()), "unique left-hand sides in substitutees " + this)

  /** unique left hand sides in subsDefs */
  private def dataStructureInvariant(): Unit = {
    // check that we never replace n by something and then again replacing the same n by something
    // this check is redundant except that it also yells at {p(.)~>.>=0,p(.)~>p(.)}
    val lefts = subsDefsInput.map(_.what).toList
    insist(lefts.distinct.size == lefts.size, "conflict: no duplicate substitutions for the same substitutee " + subsDefsInput)
    // check that we never replace p(x) by something and also p(t) by something
    val lambdaNames = matchKeys
    insist(lambdaNames.distinct.size == lambdaNames.size, "conflict: no duplicate substitutions for the same substitutee (modulo renaming) " + this)
  }

  override def toString: String = "USubstOne{" + subsDefs.mkString(", ") + "}"

  /**
    * The (new) free variables that this substitution introduces (without DotTerm/DotFormula arguments).
    * That is the (new) free variables introduced by this substitution, i.e.
    * free variables of all repl that are not bound as arguments in what.
    * @return union of the freeVars of all our substitution pairs.
    * @note unused
    */
  lazy val freeVars: SetLattice[Variable] = subsDefs.foldLeft(bottom[Variable])((a,b) => a ++ b.freeVars)

  /**
    * The signature of the replacement introduced by this substitution.
    * @return union of the freeVars of all our substitution pairs.
    */
  //lazy val signature: immutable.Set[NamedSymbol] = subsDefs.foldLeft(Set.empty[NamedSymbol])((a,b) => a ++ b.signature)

  /**
    * The key characteristic expression constituents that this Substitution is matching on.
    * @return union of the matchKeys of all our substitution pairs.
    */
  private[core] lazy val matchKeys: immutable.List[NamedSymbol] =
    subsDefs.foldLeft(immutable.List[NamedSymbol]())((a,b) => a :+ b.matchKey)


  // apply calls usubst, augmenting with contract and exception context handling

  def apply(e: Expression): Expression = e match {
    case t: Term => apply(t)
    case f: Formula => apply(f)
    //@note This case happens for standalone uniform substitutions on differential programs such as x'=f() or c as they come up in unification for example.
    case p: DifferentialProgram => apply(p)
    case p: Program => apply(p)
    case f: Function => throw SubstitutionClashException(toString, "", e.toString, "", "", "substitutions are not defined on an isolated Function that is not applied to arguments.")
  }

  //@note could define a direct composition implementation for fast compositions of USubst, but not used.

  /** apply this uniform substitution everywhere in a term
    * @throws SubstitutionClashException if this substitution is not admissible for t.
    */
  //@note optimizable for empty subsDefs if that happens often (unlikely)
  def apply(t: Term): Term = try usubst(bottom, t) catch {case ex: ProverException => throw ex.inContext(t.prettyString)}
  /** apply this uniform substitution everywhere in a formula
    * @throws SubstitutionClashException if this substitution is not admissible for f.
    */
  def apply(f: Formula): Formula = try usubst(bottom, f) catch {case ex: ProverException => throw ex.inContext(f.prettyString)}
  /** apply this uniform substitution everywhere in a program
    * @throws SubstitutionClashException if this substitution is not admissible for p.
    */
  def apply(p: Program): Program = try usubst(bottom[Variable], p)._2 catch {case ex: ProverException => throw ex.inContext(p.prettyString)}
  /** apply this uniform substitution everywhere in a differential program
    * @throws SubstitutionClashException if this substitution is not admissible for p.
    */
  def apply(p: DifferentialProgram): DifferentialProgram = try usubstODE(boundVars(p), p) catch {case ex: ProverException => throw ex.inContext(p.prettyString)}

  /**
    * Apply uniform substitution everywhere in the sequent.
    * @throws SubstitutionClashException if this substitution is not admissible for s.
    */
  //@note mapping apply instead of the equivalent usubst makes sure the exceptions are augmented with formula context
  def apply(s: Sequent): Sequent = try { Sequent(s.ante.map(apply), s.succ.map(apply)) } catch { case ex: ProverException => throw ex.inContext(s.toString) }


  /** apply this uniform substitution everywhere in a formula with [[SetLattice.allVars]] as taboos.
    * @throws SubstitutionClashException if this substitution is not admissible for f (e.g. because it introduces any free variables).
    */
  def applyAllTaboo(f: Formula): Formula = try usubst(allVars, f) catch {case ex: ProverException => throw ex.inContext(f.prettyString)}

  /**
    * Apply uniform substitution everywhere in the sequent with [[SetLattice.allVars]] as taboos.
    * @throws SubstitutionClashException if this substitution is not admissible for s (e.g. because it introduces any free variables).
    */
  //@note mapping apply instead of the equivalent usubst makes sure the exceptions are augmented and the ensures contracts checked.
  def applyAllTaboo(s: Sequent): Sequent = try { Sequent(s.ante.map(applyAllTaboo), s.succ.map(applyAllTaboo)) } catch { case ex: ProverException => throw ex.inContext(s.toString) }


  /** Union of uniform substitutions, i.e., both replacement lists merged.
    * @note Convenience method not used in the core, but used for stapling uniform substitutions together during unification etc.
    */
  //@todo optimizable since most of the data structure invariant, filtering, and individual distinctness is already checked
  def ++(other: USubstOne): USubstOne = USubstOne((this.subsDefs ++ other.subsDefs).distinct)


  // implementation of uniform substitution application
  //@see Figure 2 in Andre Platzer. [[https://doi.org/10.1007/978-3-030-29436-6_25 Uniform substitution at one fell swoop]]. In Pascal Fontaine, editor, International Conference on Automated Deduction, CADE'19, Natal, Brazil, Proceedings, volume 11716 of LNCS, pp. 425-441. Springer, 2019.

  /** uniform substitution on terms.
    * @param u the set of variables that are taboo, so cannot be introduced free by the substitution into term. */
  private def usubst(u: SetLattice[Variable], term: Term): Term = {
    term match {
      // uniform substitution base cases
      case x: Variable => x
      case app@FuncOf(f, theta) => subsDefs.find(sp => sp.what.isInstanceOf[FuncOf] && sp.sameHead(app)) match {
          case Some(subs) =>
            val FuncOf(wf, wArg) = subs.what
            //redundant: assert(wf == f, "match on same function heads")
            //redundant: assert(SubstitutionAdmissibility.isSubstitutableArg(wArg))
            requireAdmissible(u, subs.freeVars, subs.repl, term)
            // unofficial substitution for Nothing (no effect) and Anything in analogy to substitution for DotTerm
            //@note Uniform substitution of the argument placeholder applied to the replacement subs.repl for the shape subs.what
            USubstOne(toSubsPairs(u, wArg, theta)).usubst(bottom[Variable], subs.repl.asInstanceOf[Term])
          case None => FuncOf(f, usubst(u, theta))
        }
      case Nothing => Nothing
        //redundant: assert(!subsDefs.exists(sp => sp.what == Nothing /*&& sp.repl != Nothing*/), "can replace Nothing only by Nothing, and nothing else");
      case d: DotTerm => subsDefs.find(_.what==d) match {
        case Some(subs) =>
          requireAdmissible(u, subs.freeVars, subs.repl, d)
          subs.repl.asInstanceOf[Term]
        case None => d
      }
      case n: Number => n
      //@note except for Differential, the following cases are equivalent to f.reapply but are left explicit to enforce revisiting this case when data structure changes.
      // case f:BinaryCompositeTerm => f.reapply(usubst(f.left), usubst(f.right))
      // homomorphic cases
      case Neg(e) => Neg(usubst(u, e))
      case Plus(l, r)   => Plus(usubst(u, l),   usubst(u, r))
      case Minus(l, r)  => Minus(usubst(u, l),  usubst(u, r))
      case Times(l, r)  => Times(usubst(u, l),  usubst(u, r))
      case Divide(l, r) => Divide(usubst(u, l), usubst(u, r))
      case Power(l, r)  => Power(usubst(u, l),  usubst(u, r))
      case Differential(e) => Differential(usubst(allVars, e))
      // unofficial
      case Pair(l, r) => Pair(usubst(u, l), usubst(u, r))
      case f: UnitFunctional => subsDefs.find(_.what==f) match {
        case Some(subs) => subs.repl.asInstanceOf[Term]
        case None => f
      }
    }
  }


  /** uniform substitution on formulas.
    * @param u the set of variables that are taboo, so cannot be introduced free by the substitution into formula. */
  private def usubst(u: SetLattice[Variable], formula: Formula): Formula = {
    formula match {
      case app@PredOf(p, theta) => subsDefs.find(sp => sp.what.isInstanceOf[PredOf] && sp.sameHead(app)) match {
        case Some(subs) =>
          val PredOf(wp, wArg) = subs.what
          //redundant: assert(wp == p, "match only if same head")
          //redundant: assert(SubstitutionAdmissibility.isSubstitutableArg(wArg))
          requireAdmissible(u, subs.freeVars, subs.repl, formula)
          // unofficial substitution for Nothing (no effect) and Anything in analogy to substitution for DotTerm
          //@note Uniform substitution of the argument placeholder applied to the replacement subs.repl for the shape subs.what
          USubstOne(toSubsPairs(u, wArg, theta)).usubst(bottom[Variable], subs.repl.asInstanceOf[Formula])
        case None => PredOf(p, usubst(u, theta))
      }
      // unofficial
      case app@PredicationalOf(p, fml) => subsDefs.find(sp => sp.what.isInstanceOf[PredicationalOf] && sp.sameHead(app)) match {
        case Some(subs) =>
          //@note val PredicationalOf(_, DotFormula) = subs.what is easier to read even if possibly a little slower
          val PredicationalOf(wp, wArg) = subs.what
          //redundant: assert(wp == p, "match only if same head")
          //redundant: assert(wArg == DotFormula)
          USubstOne(SubstitutionPair(wArg, usubst(allVars, fml)) :: Nil).usubst(bottom[Variable], subs.repl.asInstanceOf[Formula])
        case None =>
          //@note admissibility is required for nonmatching predicationals since the arguments might be evaluated in different states.
          PredicationalOf(p, usubst(allVars, fml))
      }
      case DotFormula => subsDefs.find(_.what == DotFormula) match {
        case Some(subs) => subs.repl.asInstanceOf[Formula]
        case None => DotFormula
      }
      case True | False => formula

      //@note except for DifferentialFormula, the following cases are equivalent to f.reapply but are left explicit to enforce revisiting this case when data structure changes.
      // case f:BinaryCompositeTerm => f.reapply(usubst(f.left), usubst(f.right))

      // pseudo-homomorphic cases
      case Equal(l, r)        => Equal(usubst(u, l), usubst(u, r))
      case NotEqual(l, r)     => NotEqual(usubst(u, l), usubst(u, r))
      case GreaterEqual(l, r) => GreaterEqual(usubst(u, l), usubst(u, r))
      case Greater(l, r)      => Greater(usubst(u, l), usubst(u, r))
      case LessEqual(l, r)    => LessEqual(usubst(u, l), usubst(u, r))
      case Less(l, r)         => Less(usubst(u, l), usubst(u, r))

      // homomorphic cases
      case Not(g)      => Not(usubst(u, g))
      case And(l, r)   => And(usubst(u, l), usubst(u, r))
      case Or(l, r)    => Or(usubst(u, l), usubst(u, r))
      case Imply(l, r) => Imply(usubst(u, l), usubst(u, r))
      case Equiv(l, r) => Equiv(usubst(u, l), usubst(u, r))

      // NOTE DifferentialFormula in analogy to Differential
      case DifferentialFormula(g) => DifferentialFormula(usubst(allVars, g))

      // binding cases add bound variables to u
      case Forall(vars, g) => Forall(vars, usubst(u++vars, g))
      case Exists(vars, g) => Exists(vars, usubst(u++vars, g))

      case Box(p, g)     => val (v,rp) = usubst(u,p); Box(rp, usubst(v,g))
      case Diamond(p, g) => val (v,rp) = usubst(u,p); Diamond(rp, usubst(v,g))
      case p: UnitPredicational => subsDefs.find(_.what==p) match {
        case Some(subs) => subs.repl.asInstanceOf[Formula]
        case None => p
      }
    }
  }

  /** uniform substitution on programs.
    * @param u the set of variables that are taboo, so cannot be introduced free by the substitution into program. */
  private def usubst(u: SetLattice[Variable], program: Program): (SetLattice[Variable],Program) = {
    program match {
      case a: ProgramConst => subsDefs.find(_.what == a) match {
        case Some(subs) => (u++subs.boundVars, subs.repl.asInstanceOf[Program])
        case None       => (StaticSemantics.spaceVars(a.space), a)
      }
      case a: SystemConst => subsDefs.find(_.what == a) match {
        case Some(subs) => (u++subs.boundVars, subs.repl.asInstanceOf[Program])
        case None       => (StaticSemantics.spaceVars(a.space), a)
      }
      case Assign(x, e)      => (u+x, Assign(x, usubst(u,e)))
      case a@AssignAny(x)    => (u+x, a)
      case Test(f)           => (u, Test(usubst(u,f)))
      case ODESystem(ode, h) =>
        val v = u++substBoundVars(ode)
        (v, ODESystem(usubstODE(v, ode), usubst(v, h)))
      case Choice(a, b)      => val (v,ra) = usubst(u,a); val (w,rb) = usubst(u,b); (v++w, Choice(ra, rb))
      case Compose(a, b)     => val (v,ra) = usubst(u,a); val (w,rb) = usubst(v,b); (w, Compose(ra, rb))
      // unoptimized version:  //case Loop(a) if!optima => val (v,_)  = usubst(u,a); val (_,ra) = usubst(v,a); (v, Loop(ra))
      // optimized version:
      case Loop(a)           => val v = u++substBoundVars(a); val (w,ra) = usubst(v,a);
        //@note optimizable checking v==w is redundant but avoids making substBoundVars soundness-critical
        if (v==w) (v, Loop(ra)) else {val (_,rb) = usubst(w, a); (w, Loop(rb))}
      case Dual(a)           => val (v,ra) = usubst(u,a); (v, Dual(ra))

      // `DifferentialProgram`s must be wrapped in an `ODESystem` when used as a `Program`
      case dp: AtomicODE => throw MalformedProgramException(dp)
      case dp: DifferentialProgramConst => throw MalformedProgramException(dp)
      case dp: DifferentialProduct => throw MalformedProgramException(dp)
    }
  }

  /** uniform substitutions on differential programs.
    * @param v the set of variables that are taboo (including the surrounding ODESystem), so cannot be introduced free by the substitution into ode. */
  private def usubstODE(v: SetLattice[Variable], ode: DifferentialProgram): DifferentialProgram = {
    ode match {
      case AtomicODE(xp: DifferentialSymbol, e) =>
        assert(v.contains(xp) && v.contains(xp.x), "all bound variables already added to ODE taboos")
        AtomicODE(xp, usubst(v, e))
      case c: DifferentialProgramConst => subsDefs.find(_.what == c) match {
        //@note Space compliance already checked in SubstitutionPair construction.
        case Some(subs) => subs.repl.asInstanceOf[DifferentialProgram]
        case None       => c
      }
      // homomorphic cases
      case DifferentialProduct(a, b) => DifferentialProduct(usubstODE(v, a), usubstODE(v, b))
    }
  }


  // admissibility

  /**
    * Require that this uniform substitution is admissible with the given taboos for expression e, and
    * raise informative exception if not.
    * @throws SubstitutionClashException if `!taboo.intersect(frees).isEmpty`
    */
  @inline private def requireAdmissible(taboo: SetLattice[Variable], frees: SetLattice[Variable], e: Expression, context: Expression): Unit = {
    val clashes = taboo.intersect(frees)
    if (!clashes.isEmpty)
      throw SubstitutionClashException(toString, taboo.prettyString, e.prettyString, context.prettyString, clashes.prettyString, "")
  }

  /** Turns matching terms into substitution pairs (traverses pairs to create component-wise substitutions).
    * @return The SubstitutionPair `w ~> usubst(taboo, r)` or such substitutions on the components in case w and r are Pairs. */
  private def toSubsPairs(taboo: SetLattice[Variable], w: Term, r: Term): List[SubstitutionPair] = (w, r) match {
    case (Pair(wl, wr), Pair(rl, rr)) => toSubsPairs(taboo, wl, rl) ++ toSubsPairs(taboo, wr, rr)
    case _ => SubstitutionPair(w, usubst(taboo, r)) :: Nil
  }


  // optimization

  /** Predict bound variables of this(program), whether substitution clashes or not.
    * @note Not soundness-critical as result is checked by inclusion for second usubst round
    * @note Like [[StaticSemantics.boundVars()]] except with replaced program constant symbols etc computed from their bound variables. */
  private def substBoundVars(program: Program): SetLattice[Variable] = {
    program match {
      // base cases
      case a: ProgramConst => subsDefs.find(_.what == a) match {
        case Some(subs) => subs.boundVars
        case None       => StaticSemantics.spaceVars(a.space)
      }
      case a: SystemConst  => subsDefs.find(_.what == a) match {
        case Some(subs) => subs.boundVars
        case None       => StaticSemantics.spaceVars(a.space)
      }
      case c: DifferentialProgramConst => subsDefs.find(_.what == c) match {
        case Some(subs) => subs.boundVars
        case None       => StaticSemantics.spaceVars(c.space)
      }
      case Assign(x, e)                => SetLattice(x)
      case Test(f)                     => bottom
      case AtomicODE(xp@DifferentialSymbol(x), e) => SetLattice(Set(x,xp))
      // combinator cases
      case Choice(a, b)                => substBoundVars(a) ++ substBoundVars(b)
      case Compose(a, b)               => substBoundVars(a) ++ substBoundVars(b)
      case Loop(a)                     => substBoundVars(a)
      case Dual(a)                     => substBoundVars(a)

      // special cases
      //@note x:=* in analogy to x:=e
      case AssignAny(x)                => SetLattice(x)
      //@note system generalization of x'=e&h
      case ODESystem(a, h)             => substBoundVars(a)
      case DifferentialProduct(a, b)   => substBoundVars(a) ++ substBoundVars(b)
    }
  }
}
