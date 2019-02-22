package edu.cmu.cs.ls.keymaerax.core

import scala.collection.immutable
import StaticSemantics.freeVars
import StaticSemantics.boundVars
import SetLattice.allVars
import SetLattice.bottom

/**
  * A Uniform Substitution with its one-pass application mechanism.
  * A Uniform Substitution uniformly replaces all occurrences of a given predicate p(.) by a formula in (.).
  * It can also replace all occurrences of a function symbol f(.) by a term in (.)
  * and all occurrences of a quantifier symbols C(-) by a formula in (-)
  * and all occurrences of program constant b by a hybrid program.
  *
  * This type implements the application of uniform substitutions to terms, formulas, programs, and sequents.
  *
  * @note Implements the onepassversion that checks admissibility on the fly and checking upon occurrence.
  * @note soundness-critical
  * @author Andre Platzer
  * Created by aplatzer on 2019-2-12.
  */
final case class USubstOne(subsDefsInput: immutable.Seq[SubstitutionPair]) extends (Expression => Expression) {
  /** automatically filter out identity substitution no-ops, which can happen by systematic constructions such as unification */
  private/*[this]*/ val subsDefs: immutable.Seq[SubstitutionPair] = subsDefsInput.filter(p => p.what != p.repl)

  @inline
  private val optima = true

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
  }

  //@note could define a direct composition implementation for fast compositions of USubst, but not used.

  /** apply this uniform substitution everywhere in a term */
  //@todo could optimize empty subsDefs to be identity right away if that happens often (unlikely)
  def apply(t: Term): Term = try usubst(bottom, t) catch {case ex: ProverException => throw ex.inContext(t.prettyString)}
  /** apply this uniform substitution everywhere in a formula */
  def apply(f: Formula): Formula = try usubst(bottom, f) catch {case ex: ProverException => throw ex.inContext(f.prettyString)}
  /** apply this uniform substitution everywhere in a program */
  def apply(p: Program): Program = try usubst(bottom[Variable], p)._2 catch {case ex: ProverException => throw ex.inContext(p.prettyString)}
  /** apply this uniform substitution everywhere in a differential program */
  def apply(p: DifferentialProgram): DifferentialProgram = try usubstODE(boundVars(p), p).asInstanceOf[DifferentialProgram] catch {case ex: ProverException => throw ex.inContext(p.prettyString)}

  /**
    * Apply uniform substitution everywhere in the sequent.
    */
  //@note mapping apply instead of the equivalent usubst makes sure the exceptions are augmented and the ensuring contracts checked.
  def apply(s: Sequent): Sequent = try { Sequent(s.ante.map(apply), s.succ.map(apply)) } catch { case ex: ProverException => throw ex.inContext(s.toString) }


  /** apply this uniform substitution everywhere in a formula with allVariables as taboos */
  def applyAllTaboo(f: Formula): Formula = try usubst(allVars, f) catch {case ex: ProverException => throw ex.inContext(f.prettyString)}

  /**
    * Apply uniform substitution everywhere in the sequent with allVariables as taboos.
    */
  //@note mapping apply instead of the equivalent usubst makes sure the exceptions are augmented and the ensuring contracts checked.
  def applyAllTaboo(s: Sequent): Sequent = try { Sequent(s.ante.map(applyAllTaboo(_)), s.succ.map(applyAllTaboo(_))) } catch { case ex: ProverException => throw ex.inContext(s.toString) }


  /** Union of uniform substitutions, i.e., both replacement lists merged.
    * @note Convenience method not used in the core, but used for stapling uniform substitutions together during unification etc.
    */
  def ++(other: USubstOne): USubstOne = USubstOne((this.subsDefs ++ other.subsDefs).distinct)


  /**
    * Whether this substitution matches to replace the given expression e,
    * because there is a substitution pair that matches e.
    */
  @inline private def matchHead(e: ApplicationOf): Boolean =
  subsDefs.exists(sp => sp.what.isInstanceOf[ApplicationOf] && sp.sameHead(e))

  // implementation of uniform substitution application

  /** uniform substitution on terms */
  private def usubst(u: SetLattice[Variable], term: Term): Term = {
    term match {
      // uniform substitution base cases
      case x: Variable => x
      case app@FuncOf(of, theta) if matchHead(app) =>
        val subs = uniqueElementOf[SubstitutionPair](subsDefs, sp => sp.what.isInstanceOf[FuncOf] && sp.sameHead(app))
        val FuncOf(wf, wArg) = subs.what
        assert(wf == of, "match on same function heads")
        assert(SubstitutionAdmissibility.isSubstitutableArg(wArg))
        requireAdmissible(u, subs.freeVars, subs.repl, term)
        // unofficial substitution for Nothing (no effect) and Anything in analogy to substitution for DotTerm
        //@note Uniform substitution of the argument placeholder applied to the replacement subs.repl for the shape subs.what
        USubstOne(toSubsPairs(u, wArg, theta)).usubst(bottom[Variable], subs.repl.asInstanceOf[Term])
      case app@FuncOf(g:Function, theta) if !matchHead(app) => FuncOf(g, usubst(u, theta))
      case Nothing =>
        assert(!subsDefs.exists(sp => sp.what == Nothing /*&& sp.repl != Nothing*/), "can replace Nothing only by Nothing, and nothing else");
        Nothing
      case d: DotTerm if  subsDefs.exists(_.what==d) =>
        val subs = subsDefs.find(_.what==d).get
        requireAdmissible(u, subs.freeVars, subs.repl, term)
        subs.repl.asInstanceOf[Term]
      case d: DotTerm if !subsDefs.exists(_.what==d) => term
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
      case der@Differential(e) => Differential(usubst(allVars, e))
      // unofficial
      case Pair(l, r) => Pair(usubst(u, l), usubst(u, r))
      case f: UnitFunctional if subsDefs.exists(_.what==f) => subsDefs.find(_.what==f).get.repl.asInstanceOf[Term]
      case f: UnitFunctional if !subsDefs.exists(_.what==f) => f
    }
  }


  /** uniform substitution on formulas */
  private def usubst(u: SetLattice[Variable], formula: Formula): Formula = {
    formula match {
      case app@PredOf(op, theta) if matchHead(app) =>
        val subs = uniqueElementOf[SubstitutionPair](subsDefs, sp => sp.what.isInstanceOf[PredOf] && sp.sameHead(app))
        val PredOf(wp, wArg) = subs.what
        assert(wp == op, "match only if same head")
        assert(SubstitutionAdmissibility.isSubstitutableArg(wArg))
        requireAdmissible(u, subs.freeVars, subs.repl, formula)
        // unofficial substitution for Nothing (no effect) and Anything in analogy to substitution for DotTerm
        //@note Uniform substitution of the argument placeholder applied to the replacement subs.repl for the shape subs.what
        USubstOne(toSubsPairs(u, wArg, theta)).usubst(bottom[Variable], subs.repl.asInstanceOf[Formula])
      case app@PredOf(q, theta) if !matchHead(app) => PredOf(q, usubst(u, theta))
      // unofficial
      case app@PredicationalOf(op, fml) if matchHead(app) =>
        val subs = uniqueElementOf[SubstitutionPair](subsDefs, sp => sp.what.isInstanceOf[PredicationalOf] && sp.sameHead(app))
        val PredicationalOf(wp, wArg) = subs.what
        assert(wp == op, "match only if same head")
        assert(wArg == DotFormula)
        USubstOne(SubstitutionPair(wArg, usubst(allVars, fml)) :: Nil).usubst(bottom[Variable], subs.repl.asInstanceOf[Formula])
      // unofficial
      case app@PredicationalOf(q, fml) if !matchHead(app) =>
        //@note admissibility is required for nonmatching predicationals since the arguments might be evaluated in different states.
        PredicationalOf(q, usubst(allVars, fml))
      case DotFormula if  subsDefs.exists(_.what == DotFormula) =>
        subsDefs.find(_.what == DotFormula).get.repl.asInstanceOf[Formula]
      case DotFormula if !subsDefs.exists(_.what == DotFormula) => DotFormula
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
      case der@DifferentialFormula(g) => DifferentialFormula(usubst(allVars, g))

      // binding cases add bound variables to u
      case Forall(vars, g) => Forall(vars, usubst(u++vars, g))
      case Exists(vars, g) => Exists(vars, usubst(u++vars, g))

      case Box(p, g)     => val (v,rp) = usubst(u,p); Box(rp, usubst(v,g))
      case Diamond(p, g) => val (v,rp) = usubst(u,p); Diamond(rp, usubst(v,g))
      case p: UnitPredicational if subsDefs.exists(_.what==p) => subsDefs.find(_.what==p).get.repl.asInstanceOf[Formula]
      case p: UnitPredicational if !subsDefs.exists(_.what==p) => p
    }
  }

  /** uniform substitution on programs */
  private def usubst(u: SetLattice[Variable], program: Program): (SetLattice[Variable],Program) = {
    program match {
      case a: ProgramConst if subsDefs.exists(_.what == a) =>
        val r = subsDefs.find(_.what == a).get.repl.asInstanceOf[Program]
        (u++boundVars(r), r)
      //@todo optimizable: store boundVars(ProgramConst/SystemConst/DifferentialProgramConst) in substitution pair
      //@todo improve: for ProgramConst(_,Taboo(except)) could return allVars-except
      case a: ProgramConst if !subsDefs.exists(_.what == a) => (allVars, a)
      case a: SystemConst  if subsDefs.exists(_.what == a) =>
        val r = subsDefs.find(_.what == a).get.repl.asInstanceOf[Program]
        (u++boundVars(r), r)
      case a: SystemConst  if !subsDefs.exists(_.what == a) => (allVars, a)
      case Assign(x, e)      => (u+x, Assign(x, usubst(u,e)))
      case AssignAny(x)      => (u+x, program)
      case Test(f)           => (u, Test(usubst(u,f)))
      case ODESystem(ode, h) =>
        //@todo improve: could make smaller for substituted DifferentialProgramConst
        val v = u++boundVars(ode)
        (v, ODESystem(usubstODE(v, ode), usubst(v, h)))
      case Choice(a, b)      => val (v,ra) = usubst(u,a); val (w,rb) = usubst(u,b); (v++w, Choice(ra, rb))
      case Compose(a, b)     => val (v,ra) = usubst(u,a); val (w,rb) = usubst(v,b); (w, Compose(ra, rb))
      case Loop(a) if!optima => val (v,_)  = usubst(u,a); val (_,ra) = usubst(v,a); (v, Loop(ra))
      case Loop(a) if optima => val v = u++substBoundVars(a); val (w,ra) = usubst(v,a);
        // redundant: check result of substBoundVars for equality to make it not soundness-critical
        if (v==w) (v, Loop(ra)) else {val (_,rb) = usubst(w, a); (w, Loop(rb))}
      case Dual(a)           => val (v,ra) = usubst(u,a); (v, Dual(ra))
    }
  }

  /** uniform substitutions on differential programs */
  private def usubstODE(v: SetLattice[Variable], ode: DifferentialProgram): DifferentialProgram = {
    ode match {
      case AtomicODE(xp: DifferentialSymbol, e) =>
        assert(v.contains(xp) && v.contains(xp.x), "all bound variables already added to ODE taboos")
        AtomicODE(xp, usubst(v, e))
      case c: DifferentialProgramConst if subsDefs.exists(_.what == c) =>
        //@note Space compliance already checked in SubstitutionPair construction.
        subsDefs.find(_.what == c).get.repl.asInstanceOf[DifferentialProgram]
      case c: DifferentialProgramConst if !subsDefs.exists(_.what == c) => c
      // homomorphic cases
      case DifferentialProduct(a, b) => DifferentialProduct(usubstODE(v, a), usubstODE(v, b))
    }
  }


  // admissibility

  /**
    * Require that this uniform substitution is admissible with the given taboos for expression e, and
    * raise informative exception if not.
    */
  @inline private def requireAdmissible(taboo: SetLattice[Variable], frees: SetLattice[Variable], e: Expression, context: Expression): Unit = {
    val clashes = taboo.intersect(frees)
    if (!clashes.isEmpty)
      throw new SubstitutionClashException(toString, taboo.prettyString, e.prettyString, context.prettyString, clashes.prettyString, "")
  }

  /** Turns matching terms into substitution pairs (traverses pairs to create component-wise substitutions). */
  private def toSubsPairs(taboo: SetLattice[Variable], w: Term, r: Term): List[SubstitutionPair] = (w, r) match {
    case (Pair(wl, wr), Pair(rl, rr)) => toSubsPairs(taboo, wl, rl) ++ toSubsPairs(taboo, wr, rr)
    case _ => SubstitutionPair(w, usubst(taboo, r)) :: Nil
  }

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

  // optimization

  /** Predict bound variables of this(program), whether substitution clashes or not.
    * @note Not soundness-critical as result checked by inclusion for other usubst round */
  private def substBoundVars(program: Program): SetLattice[Variable] = {
    program match {
      // base cases
      //@todo optimizable: store boundVars(ProgramConst/SystemConst/DifferentialProgramConst) in substitution pair
      case a: ProgramConst if subsDefs.exists(_.what == a) =>
        StaticSemantics.boundVars(subsDefs.find(_.what == a).get.repl.asInstanceOf[Program])
      case a: ProgramConst if !subsDefs.exists(_.what == a) => StaticSemantics.spaceVars(a.space)
      case a: SystemConst  if subsDefs.exists(_.what == a) =>
        StaticSemantics.boundVars(subsDefs.find(_.what == a).get.repl.asInstanceOf[Program])
      case a: SystemConst  if !subsDefs.exists(_.what == a) => allVars
      case c: DifferentialProgramConst if subsDefs.exists(_.what == c) =>
        StaticSemantics.boundVars(subsDefs.find(_.what == c).get.repl.asInstanceOf[DifferentialProgram])
      case c: DifferentialProgramConst if !subsDefs.exists(_.what == c) => StaticSemantics.spaceVars(c.space)
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
