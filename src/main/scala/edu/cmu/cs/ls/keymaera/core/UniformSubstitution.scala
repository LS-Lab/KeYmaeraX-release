/**
 * Uniform Substitution for KeYmaera
 * @author aplatzer
 * @author smitsch
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

/**
 * A Uniform Substitution with its application mechanism.
 * Implements application of uniform substitutions to terms, formulas, programs.
 * "Global" version that checks admissibility eagerly at bound variables rather than computing bounds on the fly and checking upon occurrence.
 * Used for UniformSubstitution rule.
 * @author aplatzer
 */
final case class USubst(subsDefs: scala.collection.immutable.Seq[SubstitutionPair]) {
  applicable()

  // unique left hand sides in l
  @elidable(ASSERTION) def applicable() = {
    // check that we never replace n by something and then again replacing the same n by something
    val lefts = subsDefs.map(_.what).toList
    require(lefts.distinct.size == lefts.size, "no duplicate substitutions with same substitutees " + subsDefs)
    // check that we never replace p(x) by something and also p(t) by something
    val lambdaNames = subsDefs.map(_.what match {
      case ApplyPredicate(p: Function, _: Variable) => List(p)
      case Apply(f: Function, _: Variable) => List(f)
      case _ => Nil
    }).fold(Nil)((a,b) => a++b)
    require(lambdaNames.distinct.size == lambdaNames.size, "no duplicate substitutions with same substitutee modulo alpha-renaming of lambda terms " + subsDefs)
  }

  @elidable(FINEST-1) private def log(msg: =>String) {}  //= println(msg)

  override def toString: String = "USubst(" + subsDefs.mkString(", ") + ")"

  def apply(t: Term): Term = {
    usubst(t)
  } ensuring(_ == new FastUSubst(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], t),
    s"USubst result ${usubst(t)} does not agree with fast result " +
      s"${new FastUSubst(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], t)}")
  def apply(f: Formula): Formula = {
    usubst(f)
  } ensuring(_ == new FastUSubst(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], f),
    s"USubst result ${usubst(f)} does not agree with fast result " +
      s"${new FastUSubst(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], f)}")
  def apply(p: Program): Program = {
    usubst(p)
  } ensuring(_ == new FastUSubst(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], p).p,
    s"USubst result ${usubst(p)} does not agree with fast result " +
      s"${new FastUSubst(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], p)}")

  /**
   * Apply uniform substitution everywhere in the sequent.
   */
  def apply(s: Sequent): Sequent = {
    try {
      Sequent(s.pref, s.ante.map(apply), s.succ.map(apply))
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this, null, s.toString()).initCause(ex)
    }
  }

  // implementation of uniform substitution application
      
  // uniform substitution on terms
  private[core] def usubst(t: Term): Term = {
    try {
      t match {
        // uniform substitution base cases
        case x: Variable => require(!subsDefs.exists(_.what == x), s"Substitution of variables not supported: $x"); x
        case xp@Derivative(Real, x: Variable) => require(!subsDefs.exists(_.what == xp),
          s"Substitution of differential symbols not supported: $xp"); xp
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
          USubst(SubstitutionPair(rArg, usubst(theta)) :: Nil).usubst(rTerm)
        case app@Apply(g, theta) if !subsDefs.exists(sameHead(_, app)) => Apply(g, usubst(theta))
        case Anything => Anything // TODO check
        case Nothing => Nothing // TODO check
        case CDot if !subsDefs.exists(_.what == CDot) => CDot // TODO check (should be case x = sigma x for variable x)
        case CDot if  subsDefs.exists(_.what == CDot) => // TODO check (should be case x = sigma x for variable x)
          subsDefs.find(_.what == CDot).get.repl match {
            case t: Term => t
            case _ => throw new IllegalArgumentException("Can only substitute terms for .")
          }
        case n@Number(_, _) => n
        //@TODO any way of ensuring for the following that top-level(t)==top-level(\result)
         // homomorphic cases
        case Neg(s, e) => Neg(s, usubst(e))
        case Add(s, l, r) => Add(s, usubst(l), usubst(r))
        case Subtract(s, l, r) => Subtract(s, usubst(l), usubst(r))
        case Multiply(s, l, r) => Multiply(s, usubst(l), usubst(r))
        case Divide(s, l, r) => Divide(s, usubst(l), usubst(r))
        case Exp(s, l, r) => Exp(s, usubst(l), usubst(r))
        case der@Derivative(Real, e) =>
          require(admissible(SetLattice.top[NamedSymbol], e),
            s"Substitution clash when substituting derivative ${der.prettyString()}: static semantics of $e = ${StaticSemantics(e)} is not empty")
          Derivative(Real, usubst(e))
      }
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this, t, t.prettyString()).initCause(ex)
    }
  }

  private[core] def usubst(f: Formula): Formula = {
    log(s"Substituting ${f.prettyString()} using $this")
    try {
      f match {
        case app@ApplyPredicate(_, theta) if subsDefs.exists(sameHead(_, app)) =>
          val subs = uniqueElementOf[SubstitutionPair](subsDefs, sameHead(_, app))
          val (rArg, rFormula) = (
            subs.what match { case ApplyPredicate(_, v: NamedSymbol) => v
                           case _ => throw new IllegalArgumentException(
                            s"Substitution of p(theta)=${app.prettyString()} for arbitrary theta=${theta.prettyString()} not supported")},
            subs.repl match { case f: Formula => f
                           case _ => throw new IllegalArgumentException(
                             s"Can only substitute formulas for ${app.prettyString()}")
            })
          USubst(SubstitutionPair(rArg, usubst(theta)) :: Nil).usubst(rFormula)
        case app@ApplyPredicate(q, theta) if !subsDefs.exists(sameHead(_, app)) => ApplyPredicate(q, usubst(theta))
        case True | False => f

        //@TODO any way of ensuring for the following that  top-level(f)==top-level(\result)
        case Equals(d, l, r) => Equals(d, usubst(l), usubst(r))
        case NotEquals(d, l, r) => NotEquals(d, usubst(l), usubst(r))
        case GreaterEqual(d, l, r) => GreaterEqual(d, usubst(l), usubst(r))
        case GreaterThan(d, l, r) => GreaterThan(d, usubst(l), usubst(r))
        case LessEqual(d, l, r) => LessEqual(d, usubst(l), usubst(r))
        case LessThan(d, l, r) => LessThan(d, usubst(l), usubst(r))

        // homomorphic cases
        case Not(g) => Not(usubst(g))
        case And(l, r) => And(usubst(l), usubst(r))
        case Or(l, r) => Or(usubst(l), usubst(r))
        case Imply(l, r) => Imply(usubst(l), usubst(r))
        case Equiv(l, r) => Equiv(usubst(l), usubst(r))

        case der@FormulaDerivative(g) =>
          require(admissible(SetLattice.top[NamedSymbol], g),
            s"Substitution clash when substituting derivative ${der.prettyString()}")
          FormulaDerivative(usubst(g))

        // binding cases add bound variables to u
        case Forall(vars, g) => require(admissible(SetLattice(vars), g),
          s"Substitution clash: {x}=$vars when substituting forall ${g.prettyString()}")
            Forall(vars, usubst(g))
        case Exists(vars, g) => require(admissible(SetLattice(vars), g),
          s"Substitution clash: {x}=$vars when substituting exists ${g.prettyString()}")
            Exists(vars, usubst(g))

        case BoxModality(p, g) => require(admissible(StaticSemantics(usubst(p)).bv, g),
          s"Substitution clash: BV(sigma a)=${StaticSemantics(usubst(p)).bv} when substituting [${p.prettyString()}]${g.prettyString()}")
            BoxModality(usubst(p), usubst(g))
        case DiamondModality(p, g) => require(admissible(StaticSemantics(usubst(p)).bv, g),
          s"Substitution clash: BV(sigma a)=${StaticSemantics(usubst(p)).bv} when substituting <${p.prettyString()}>${g.prettyString()}")
            DiamondModality(usubst(p), usubst(g))
      }
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this, f, f.prettyString()).initCause(ex)
    }
  }

  // uniform substitution on programs
  private[core] def usubst(p: Program): Program = {
    try {
      p match {
        case a: ProgramConstant if subsDefs.exists(_.what == a) =>
          subsDefs.find(_.what == a).get.repl.asInstanceOf[Program]
        case a: ProgramConstant if !subsDefs.exists(_.what == a) => a
        case Assign(x: Variable, e) => Assign(x, usubst(e))
        case Assign(xp@Derivative(_, x: Variable), e) => Assign(xp, usubst(e))
        case NDetAssign(x: Variable) => NDetAssign(x)
        case Test(f) => Test(usubst(f))
        case ode: DifferentialProgram =>
          // require is redundant with the checks on NFContEvolve in usubst(ode, primed)
          require(admissible(StaticSemantics(ode).bv, ode),
            s"Substitution clash in ODE: {x}=${StaticSemantics(ode).bv} when substituting ${ode.prettyString()}")
          usubstODE(ode, StaticSemantics(ode).bv)
        case Choice(a, b) => Choice(usubst(a), usubst(b))
        case Sequence(a, b) => require(admissible(StaticSemantics(usubst(a)).bv, b),
          s"Substitution clash: BV(sigma a)=${StaticSemantics(usubst(a)).bv} when substituting ${a.prettyString()} ; ${b.prettyString()}")
          Sequence(usubst(a), usubst(b))
        case Loop(a) => require(admissible(StaticSemantics(usubst(a)).bv, a),
          s"Substitution clash: BV(sigma a)=${StaticSemantics(usubst(a)).bv} when substituting ${a.prettyString()} *")
          Loop(usubst(a))
      }
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this, p, p.toString()).initCause(ex)
    }
  }

  private def usubstODE(ode: DifferentialProgram, primed: SetLattice[NamedSymbol]): DifferentialProgram = ode match {
    case ODESystem(d, a, h) if d.isEmpty =>
      require(admissible(primed, h), s"Substitution clash in ODE: {x}=$primed clash with ${h.prettyString()}")
      ODESystem(d, usubstODE(a, primed), usubst(h))
    case ODESystem(d, a , h) if d.nonEmpty => throw new UnknownOperatorException("Check implementation whether passing v is correct.", ode)
    case AtomicODE(dv: Derivative, t) =>
      require(admissible(primed, t), s"Substitution clash in ODE: {x}=$primed clash with ${t.prettyString()}")
      AtomicODE(dv, usubst(t))
    case ODEProduct(a, b) => ODEProduct(usubstODE(a, primed), usubstODE(b, primed))
    case IncompleteSystem(s) => IncompleteSystem(usubstODE(s, primed))
    case CheckedContEvolveFragment(s) => CheckedContEvolveFragment(usubstODE(s, primed))
    case c: DifferentialProgramConstant if  subsDefs.exists(_.what == c) =>
      val repl = subsDefs.find(_.what == c).get.repl
      repl match {
        case replODE: DifferentialProgram => replODE
        case _ => throw new IllegalArgumentException("Can only substitute continuous programs for " +
          s"continuous program constants: $repl not allowed for $c")
      }
    case c: DifferentialProgramConstant if !subsDefs.exists(_.what == c) => c
    case _: EmptyODE => ode
  }
  
  // admissibility
  
  /**
   * Is this uniform substitution U-admissible for term t?
   */
  private def admissible(U: SetLattice[NamedSymbol], t: Term) : Boolean = admissible(U, StaticSemantics.signature(t))
  /**
   * Is this uniform substitution U-admissible for formula f?
   */
  private def admissible(U: SetLattice[NamedSymbol], f: Formula) : Boolean = admissible(U, StaticSemantics.signature(f))
  /**
   * Is this uniform substitution U-admissible for program p?
   */
  private def admissible(U: SetLattice[NamedSymbol], p: Program) : Boolean = admissible(U, StaticSemantics.signature(p))

  /**
   * check whether this substitution is U-admissible for an expression with the given occurrences of functions/predicates symbols.
   * @param U taboo list
   * @param occurrences of function and predicate symbols.
   */
  private def admissible(U: SetLattice[NamedSymbol], occurrences: Set[NamedSymbol]) : Boolean = {
    // if  no function symbol f in sigma with FV(sigma f(.)) /\ U != empty
    // and no predicate symbol p in sigma with FV(sigma p(.)) /\ U != empty
    // occurs in theta (or phi or alpha)
    def intersectsU(sigma: SubstitutionPair): Boolean = (sigma.repl match {
        case t: Term => sigma.what match {
          case Apply(_, Anything) => SetLattice.bottom[NamedSymbol]
          // if ever extended with f(x,y,z): StaticSemantics(t) -- {x,y,z}
          case Apply(f: Function, CDot) =>
            assert(t == sigma.repl)
            StaticSemantics(t) -- Set(CDot)
          case _ => StaticSemantics(t)
        }
        case f: Formula => sigma.what match {
          case ApplyPredicate(_, Anything) => SetLattice.bottom[NamedSymbol]
          // if ever extended with p(x,y,z): StaticSemantics(f) -- {x,y,z}
          case ApplyPredicate(fn: Function, CDot) =>
            assert(f == sigma.repl)
            StaticSemantics(f).fv -- Set(CDot)
          case _ => StaticSemantics(f).fv
        }
        case p: Program => SetLattice.bottom[NamedSymbol] // programs are always admissible, since their meaning doesn't depend on state
      }).intersect(U) != SetLattice.bottom

    def nameOf(symbol: Expr): NamedSymbol = symbol match {
      case Derivative(_, v: Variable) => v // TODO check
      case ApplyPredicate(fn, _) => fn
      case Apply(fn, _) => fn
      case s: NamedSymbol => s
      case _ => throw new IllegalArgumentException(s"Unexpected ${symbol.prettyString()} in substitution pair")
    }

    subsDefs.filter(sigma => intersectsU(sigma)).map(sigma => nameOf(sigma.what)).forall(fn => !occurrences.contains(fn))
  }

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
}
