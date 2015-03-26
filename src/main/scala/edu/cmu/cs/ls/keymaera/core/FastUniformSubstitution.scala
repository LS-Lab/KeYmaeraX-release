/**
 * 
 * @author Jan-David Quesel
 * @author aplatzer
 * @author nfulton
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 */
package edu.cmu.cs.ls.keymaera.core

// require favoring immutable Seqs for soundness

import scala.collection.immutable.Seq
import scala.collection.immutable.IndexedSeq

import scala.collection.immutable.List
import scala.collection.immutable.Map
import scala.collection.immutable.Set

import scala.annotation.{unspecialized, elidable}
import scala.annotation.elidable._
import edu.cmu.cs.ls.keymaera.core.Number.NumberObj

import scala.collection.GenTraversableOnce

@deprecated("Use StaticSemantics instead")
object BindingAssessment {
  import StaticSemantics._
  /**
   * Categorizes the names of formula f into free variables FV and bound variables BV.
   * @param f The formula to categorize.
   * @return The names in f categorized into free and bound names.
   */
  @deprecated("Use StaticSemantics(f) instead")
  def catVars(f: Formula) = StaticSemantics(f)
  
  /**
   * The set of all (may) free variables whose value t depends on (syntactically).
   */
  @deprecated("Use StaticSemantics(t) or StaticSemantics.freeVars(t) instead")
  def freeVariables(t: Term): SetLattice[NamedSymbol] = StaticSemantics(t)

  @deprecated("Use StaticSemantics(p) instead")
  def catVars(p: Program) = StaticSemantics(p)

  def primedVariables(ode: DifferentialProgram): Set[NamedSymbol] = ode match {
    case CheckedContEvolveFragment(child) => primedVariables(child) //@todo eisegesis
    case ODEProduct(a, b) => primedVariables(a) ++ primedVariables(b)
    case ODESystem(_, child, _) => primedVariables(child)
    case IncompleteSystem(a) => primedVariables(a)
    case AtomicODE(Derivative(_, x: Variable), _) => Set(x)
    case _: EmptyODE => Set.empty
    case _: DifferentialProgramConstant => Set.empty
  }

  @deprecated("Use StaticSemantics.symbols(t) instead.")
  def allNames(t: Term): Set[NamedSymbol] = StaticSemantics.symbols(t)

  @deprecated("Use StaticSemantics.symbols(f) instead.")
  def allNames(f: Formula): Set[NamedSymbol] = StaticSemantics.symbols(f)

  @deprecated("Use StaticSemantics.symbols(p) instead.")
  def allNames(p: Program): Set[NamedSymbol] = StaticSemantics.symbols(p)

  def allNamesExceptAt(s: Sequent, p: Position) = {
    val fs = if (p.isAnte) s.ante.slice(0, p.index) ++ s.ante.slice(p.index + 1, s.ante.length) ++ s.succ
             else s.ante ++ s.succ.slice(0, p.index) ++ s.succ.slice(p.index + 1, s.ante.length)
    fs.flatMap(BindingAssessment.allNames).toSet
  }
}


/**
 * A fast(?) implementation of Uniform Substitution.
 * Implementation of applying uniform substitutions to terms, formulas, programs.
 * Fast application explicit construction computing bound variables on the fly.
 * Used for UniformSubstitution rule.
 * @author aplatzer
 * @author Stefan Mitsch
 * @TODO Rename to FastSubstitution
 */
final case class FastUSubst(subsDefs: scala.collection.immutable.Seq[SubstitutionPair]) {
  applicable

  import BindingAssessment._

  /**
   * Records the result of uniform substitution in a program.
   * @param o The ignore set.
   * @param u The taboo set.
   * @param p The program.
   */
  private[core] sealed case class USR(o: SetLattice[NamedSymbol],
                        u: SetLattice[NamedSymbol],
                        p: Program)

  /**
   * @param rarg the argument in the substitution.
   * @param instArg the argument to instantiate rarg with in the occurrence.
   */
  private def instantiate(rarg: Term, instArg: Term) = new FastUSubst(List(new SubstitutionPair(rarg, instArg)))

  // unique left hand sides in l
  @elidable(ASSERTION) def applicable = {
    // check that we never replace n by something and then again replacing the same n by something
    val lefts = subsDefs.map(sp=>sp.what).toList
    require(lefts.distinct.size == lefts.size, "no duplicate substitutions with same substitutees " + subsDefs)
    // check that we never replace p(x) by something and also p(t) by something
    val lambdaNames = subsDefs.map(sp=>sp.what match {
      case ApplyPredicate(p:Function, _:Variable) => List(p)
      case Apply(f:Function, _:Variable) => List(f)
      case _ => Nil
      }).fold(Nil)((a,b)=>a++b)
      //@TODO check that we never replace p(x) by something and also p(t) by something
    require(lambdaNames.distinct.size == lambdaNames.size, "no duplicate substitutions with same substitutee modulo alpha-renaming of lambda terms " + subsDefs)
  }
  
  @elidable(FINEST-1) private def log(msg: =>String) {}  //= println(msg)
  

  override def toString: String = "Subst(" + subsDefs.mkString(", ") + ")"

  // uniform substitution on terms
  def apply(t: Term): Term = {
    try {
      usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], t)
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this, t, t.prettyString()).initCause(ex)
    }
  } ensuring (_ == new USubst(subsDefs).usubst(t),
    s"Fast substitution result ${usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], t)} " +
      s"does not agree with USubst result ${new USubst(subsDefs).usubst(t)}")

  def apply(f: Formula): Formula = {
    log("\tSubstituting " + f.prettyString + " using " + this)
    try {
      val res = usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], f)
      log("\tSubstituted  " + res.prettyString)
      res
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this, f, f.prettyString()).initCause(ex)
    }
  } ensuring (_ == new USubst(subsDefs).usubst(f),
      s"Fast substitution result ${usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], f)} " +
        s"does not agree with USubst result ${new USubst(subsDefs).usubst(f)}")

  def apply(s: Sequent): Sequent = {
    try {
      Sequent(s.pref, s.ante.map(apply), s.succ.map(apply))
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this, null, s.toString()).initCause(ex)
    }
  }

  // uniform substitution on programs
  def apply(p: Program): Program = {
    try {
      usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], p).p
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this, p, p.toString()).initCause(ex)
    }
  } ensuring (_ == new USubst(subsDefs).usubst(p),
    s"Fast substitution result ${usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], p)} " +
      s"does not agree with USubst result ${new USubst(subsDefs).usubst(p)}")

  private def substDiff(s: Seq[SubstitutionPair], names: SetLattice[NamedSymbol]) =
    new FastUSubst(s.filter(_.what match { case en: NamedSymbol => !names.contains(en) case _ => true }))

  /**
   * Check whether the function in right matches with the function in left, i.e. they have the same head.
   */
  def sameHead(left: SubstitutionPair, right: Expr) = left.what match {
    case Apply(lf, CDot | Anything | Nothing) => right match { case Apply(rf, _) => lf == rf case _ => false }
    case ApplyPredicate(lf, CDot | Anything | Nothing) => right match { case ApplyPredicate(rf, _) => lf == rf case _ => false }
    case _ => false
  }

  /**
   * Get the unique element in c to which pred applies.
   * Protests if that element is not unique because pred applies to more than one element in c or if there is none.
   */
  private def uniqueElementOf[E](c: Iterable[E], pred: E => Boolean): E = {
    require(c.count(pred) == 1)
    c.filter(pred).head
  }

  /**
   * @param u the set of taboo symbols that would clash substitutions if they occurred since they have been bound outside.
   */
  private[core] def usubst(o: SetLattice[NamedSymbol], u: SetLattice[NamedSymbol], t: Term): Term = {
    def subst(t: Term) = subsDefs.find(_.what == t).get.repl.asInstanceOf[Term]
    t match {
      // homomorphic cases
      case Neg(s, e) => Neg(s, usubst(o, u, e))
      case Add(s, l, r) => Add(s, usubst(o, u, l), usubst(o, u, r))
      case Subtract(s, l, r) => Subtract(s, usubst(o, u, l), usubst(o, u, r))
      case Multiply(s, l, r) => Multiply(s, usubst(o, u, l), usubst(o, u, r))
      case Divide(s, l, r) => Divide(s, usubst(o, u, l), usubst(o, u, r))
      case Exp(s, l, r) => Exp(s, usubst(o, u, l), usubst(o, u, r))
      // TODO not mentioned in substitution
      case Pair(dom, l, r) => Pair(dom, usubst(o, u, l), usubst(o, u, r)) // @todo eisegesis
      // uniform substitution base cases
      case x: Variable => require(!subsDefs.exists(_.what == x), s"Substitution of variables not supported: $x"); x
      // TODO not mentioned in substitution
      case CDot if !subsDefs.exists(_.what == CDot) || o.contains(CDot) => CDot //@todo eisegesis
      case CDot if  substDiff(subsDefs, o).subsDefs.exists(_.what == CDot) => //@todo eisegesis
        require((SetLattice[NamedSymbol](CDot) ++ freeVariables(subst(CDot))).intersect(u).isEmpty,
          s"Substitution clash: ({CDot} ∪ ${freeVariables(subst(CDot))}) ∩ $u is not empty")
        subst(CDot)
      case dx@Derivative(s, e) => //@todo eisegesis
        // TODO what is our requirement here?
        freeVariables(usubst(o, u, e)).intersect(u).isEmpty
        Derivative(s, usubst(o, u, e))
      case app@Apply(_, theta) if subsDefs.exists(sameHead(_, app)) =>
        val subs = uniqueElementOf[SubstitutionPair](subsDefs, sameHead(_, app))
        val (rArg, rTerm) =
          (subs.what match { case Apply(_, v: NamedSymbol) => v
                          case _ => throw new IllegalArgumentException(
                            s"Substitution of f(theta)=${app.prettyString()} for arbitrary theta=$theta not supported") },
           subs.repl match { case t: Term => t
                          case _ => throw new IllegalArgumentException(
                            s"Can only substitute terms for ${app.prettyString()}")}
          )
        val restrictedU = theta match { case CDot => u case Anything => SetLattice.bottom[NamedSymbol] case _ => u-rArg }
        require(freeVariables(rTerm).intersect(restrictedU).isEmpty,
          s"Substitution clash: ${freeVariables(subs.repl.asInstanceOf[Term])} ∩ $u is not empty")
        instantiate(rArg, usubst(o, u, theta)).usubst(SetLattice.bottom, SetLattice.bottom, rTerm)
      case app@Apply(g, theta) if !subsDefs.exists(sameHead(_, app)) => Apply(g, usubst(o, u, theta))
      case Anything => Anything
      case Nothing => Nothing
      case x: Atom => x
      case _ => throw new UnknownOperatorException("Not implemented yet", t)
    }
  }

  private[core] def usubst(o: SetLattice[NamedSymbol], u: SetLattice[NamedSymbol], f: Formula): Formula = f match {
      // homomorphic cases
    case Not(g) => Not(usubst(o, u, g))
    case And(l, r) => And(usubst(o, u, l), usubst(o, u, r))
    case Or(l, r) => Or(usubst(o, u, l), usubst(o, u, r))
    case Imply(l, r) => Imply(usubst(o, u, l), usubst(o, u, r))
    case Equiv(l, r) => Equiv(usubst(o, u, l), usubst(o, u, r))

    case Equals(d, l, r) => Equals(d, usubst(o, u, l), usubst(o, u, r))
    case NotEquals(d, l, r) => NotEquals(d, usubst(o, u, l), usubst(o, u, r))
    case GreaterEqual(d, l, r) => GreaterEqual(d, usubst(o, u, l), usubst(o, u, r))
    case GreaterThan(d, l, r) => GreaterThan(d, usubst(o, u, l), usubst(o, u, r))
    case LessEqual(d, l, r) => LessEqual(d, usubst(o, u, l), usubst(o, u, r))
    case LessThan(d, l, r) => LessThan(d, usubst(o, u, l), usubst(o, u, r))

    // binding cases add bound variables to u
    case Forall(vars, g) => Forall(vars, usubst(o ++ vars, u ++ vars, g))
    case Exists(vars, g) => Exists(vars, usubst(o ++ vars, u ++ vars, g))

    case BoxModality(p, g) => val USR(q, v, sp) = usubst(o, u, p); BoxModality(sp, usubst(q, v, g))
    case DiamondModality(p, g) => val USR(q, v, sp) = usubst(o, u, p); DiamondModality(sp, usubst(q, v, g))

    // uniform substitution base cases
    case app@ApplyPredicate(_, Anything) if subsDefs.exists(sameHead(_, app)) =>
      val rFormula = uniqueElementOf[SubstitutionPair](subsDefs, sameHead(_, app)).repl.asInstanceOf[Formula]
      FastUSubst(List()).usubst(SetLattice.bottom, SetLattice.bottom, rFormula)
    case app@ApplyPredicate(_, Anything) if !subsDefs.exists(sameHead(_, app)) => f
    case app@ApplyPredicate(_, theta) if subsDefs.exists(sameHead(_, app)) =>
      val subs = uniqueElementOf[SubstitutionPair](subsDefs, sameHead(_, app))
      val (rArg, rFormula) = (
        subs.what match { case ApplyPredicate(_, v: NamedSymbol) => v
                       case _ => throw new IllegalArgumentException(
                         s"Substitution of p(theta)=${app.prettyString()} for arbitrary theta=$theta not supported")},
        subs.repl match { case f: Formula => f
                       case _ => throw new IllegalArgumentException(
                         s"Can only substitute formulas for ${app.prettyString()}")}
        )
      val restrictedU = theta match { case CDot => u case Anything => SetLattice.bottom[NamedSymbol] case _ => u-rArg }
      require(catVars(rFormula).fv.intersect(restrictedU).isEmpty,
        s"Substitution clash: ${catVars(rFormula).fv} ∩ $restrictedU is not empty")
      instantiate(rArg, usubst(o, u, theta)).usubst(SetLattice.bottom, SetLattice.bottom, rFormula)
    case app@ApplyPredicate(p, theta) if !subsDefs.exists(sameHead(_, app)) => ApplyPredicate(p, usubst(o, u, theta))
    case FormulaDerivative(g) => FormulaDerivative(usubst(o, u, g))
    case x: Atom => x
    case _ => throw new UnknownOperatorException("Not implemented yet", f)
  }

  /**
   *  uniform substitution on a program p with the set of bound variables u
   *  return only the result components of the private case class USR
   *  used for testing only, may need a better solution
   */
  private def usubstComps(o: Set[NamedSymbol], u: Set[NamedSymbol], p: Program) = {
    val r = usubst(SetLattice(o), SetLattice(u), p); (r.o, r.u, r.p)
  }

  /**
   *
   */
  private[core] def usubst(o: SetLattice[NamedSymbol], u: SetLattice[NamedSymbol], p: Program): USR = { p match {
    case Assign(x: Variable, e) => USR(o+x, u+x, Assign(x, usubst(o, u, e)))
    case Assign(d@Derivative(_, x: Variable), e) => USR(o+DifferentialSymbol(x), u+DifferentialSymbol(x), Assign(d, usubst(o, u, e))) //@todo eisegesis
    case NDetAssign(x: Variable) => USR(o+x, u+x, p)
    case Test(f) => USR(o, u, Test(usubst(o, u, f)))
    case IfThen(cond, thenT) => USR(o, u, IfThen(usubst(o,u , cond), thenT)) //@todo eisegesis
    case ode: DifferentialProgram => val x = primedVariables(ode); val sode = usubstODE(o, u, x, ode); USR(o++SetLattice(x), u++SetLattice(x), sode)
    case Sequence(a, b) => val USR(q, v, as) = usubst(o, u, a); val USR(r, w, bs) = usubst(q, v, b); USR(r, w, Sequence(as, bs))
    case Choice(a, b) =>
      val USR(q, v, as) = usubst(o, u, a); val USR(r, w, bs) = usubst(o, u, b)
      // TODO remove when proof of uniform substitution is done
      require(((q == SetLattice.bottom && v == SetLattice.top) || q == v)
        && ((r == SetLattice.bottom && w == SetLattice.top) || r == w),
        s"Programs where not all branches write the same variables are not yet supported: q=$q ==? v=$v, r=$r ==? w=$w")
      USR(q.intersect(r), v++w, Choice(as, bs))
    case Loop(a) =>
      val USR(q, v, _) = usubst(o, u, a)
      val USR(r, w, as) = usubst(o, v, a)
      // TODO remove when proof of uniform substitution is done
      require((r == SetLattice.bottom && w == SetLattice.top) || r == w,
        s"Programs where loop does not write all variables on all branches are not yet supported: r=$r ==? w=$w")
      USR(o, w, Loop(as)) ensuring (
        o.subsetOf(q), s"Non-monotonic o: $o not subset of $q") ensuring(
        q == r, s"Unstable O: $q not equal to $r") ensuring(
        u.subsetOf(v), s"Non-monotonic u: $u not subset of $v") ensuring(
        v == w, s"Unstable U: $v not equal to $w") ensuring (
        usubst(r, w, a).o == r, s"Unstable O: ${usubst(r, w, a).o} not equal to $r") ensuring(
        usubst(r, w, a).u == w, s"Unstable U: ${usubst(r, w, a).u} not equal to $w")

    //@TODO check implementation
    case a: ProgramConstant if  subsDefs.exists(_.what == p) =>
      val sigmaP = subsDefs.find(_.what == p).get.repl.asInstanceOf[Program]
      // programs don't have a side condition, since their meaning does not depend on state
      USR(o++catVars(sigmaP).mbv, u++catVars(sigmaP).bv, sigmaP)
    case a: ProgramConstant if !subsDefs.exists(_.what == p) => USR(o++catVars(a).mbv, u++catVars(a).bv, p)
    case _ => throw new UnknownOperatorException("Not implemented yet", p)
  }} ensuring (r => { val USR(q, v, _) = r; q.subsetOf(v) }, s"Result O not a subset of result U")

  /**
   * Substitution in (systems of) differential equations.
   * @param o The ignore list.
   * @param u The taboo list.
   * @param primed The primed names (all primed names in the ODE system).
   * @param p The ODE.
   * @return The substitution result.
   */
  private def usubstODE(o: SetLattice[NamedSymbol], u: SetLattice[NamedSymbol], primed: Set[NamedSymbol], p: DifferentialProgram):
    DifferentialProgram = {
    val primedPrimed : Set[NamedSymbol] = primed.map(DifferentialSymbol(_)) //primed is a list of "Variable"s that are primed; this is the list of the acutally primed variables.
    p match {
      case ODEProduct(a, b) => ODEProduct(usubstODE(o, u, primed, a), usubstODE(o, u, primed, b))
      case ODESystem(d, a, h) if d.isEmpty => ODESystem(d, usubstODE(o, u, primed, a), usubst(o ++ SetLattice(primed), u ++ SetLattice(primed), h))
      case ODESystem(d, a, h) if d.nonEmpty => throw new UnknownOperatorException("Check implementation whether passing v is correct.", p)
      case AtomicODE(d@Derivative(_, x: Variable), e) =>
        AtomicODE(d, usubst(o ++ SetLattice(primed) ++ SetLattice(primedPrimed),
          u ++ SetLattice(primed) ++ SetLattice(primedPrimed), e)) //@todo for something like x' := y' +1 we'll need to add primedPrimed to the back lists as well.
      case _: EmptyODE => p
      case IncompleteSystem(s) => IncompleteSystem(usubstODE(o, u, primed, s))
      case CheckedContEvolveFragment(s) => CheckedContEvolveFragment(usubstODE(o, u, primed, s))
      case a: DifferentialProgramConstant if subsDefs.exists(_.what == p) =>
        val repl = subsDefs.find(_.what == p).get.repl
        repl match {
          case replODE: DifferentialProgram => replODE
          case _ => throw new IllegalArgumentException("Can only substitute continuous programs for " +
            s"continuous program constants: $repl not allowed for $a")
        }
      case a: DifferentialProgramConstant if !subsDefs.exists(_.what == p) => p
    }
  }
}
