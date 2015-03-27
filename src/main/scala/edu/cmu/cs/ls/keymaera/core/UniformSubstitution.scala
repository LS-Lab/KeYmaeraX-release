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

import StaticSemantics._

/**
 * Representation of a substitution replacing n with t.
 *
 * @param what the expression to be replaced. what can have one of the following forms:
 *          - CDot
 *          - Nothing/Anything
 *          - ApplyPredicate(p:Function, CDot/Nothing/Anything)
 *          - Apply(f:Function, CDot/Nothing/Anything)
 *          - ProgramConstant/DifferentialProgramConstant
 *          - Derivative(...)
 *          - ApplyPredicational(p:Function, CDotFormula)
 *          - CDotFormula
 * @param repl the expression to be used in place of what
 @TODO Check: Turned into case class instead of having apply/unapply for simplicity.
 */
final case class SubstitutionPair (val what: Expr, val repl: Expr) {
  applicable
  // identity substitution would be correct but is usually unintended except for systematic constructions of substitutions that happen to produce identity substitutions. In order to avoid special casing, allow identity substitutions.
  //require(n != t, "Unexpected identity substitution " + n + " by equal " + t)
  
  @elidable(ASSERTION) def applicable = {
    // identity substitution would be correct but is usually unintended except for systematic constructions of substitutions that happen to produce identity substitutions. In order to avoid special casing, allow identity substitutions.
    if(false) { //@todo Nathan suppressed this for now...
      if (what == repl) println("INFO: Unnecessary identity substitution " + what + " by equal " + repl + "\n(non-critical, just indicates a possible tactics inefficiency)")
    }
    require(what.sort == repl.sort, "Sorts have to match in substitution pairs: " + what.sort + " != " + repl.sort)
    require(what match {
     case _: Term => repl.isInstanceOf[Term]
     case _: Formula => repl.isInstanceOf[Formula]
     case _: Program => repl.isInstanceOf[Program]
    }, "substitution to same kind of expression (terms for terms, formulas for formulas, programs for programs) " + this + " substitutes " + kindOf(what) + " ~> " + kindOf(repl))
    require(what match {
      case CDot => true
      case Anything => true
      case _:ProgramConstant => true
      case _:DifferentialProgramConstant => true
      case Derivative(_, _:Variable) => true
      case Apply(_:Function, CDot | Nothing | Anything) => true
      case ApplyPredicate(_:Function, CDot | Nothing | Anything) => true
      case Nothing => repl == Nothing
      case CDotFormula => true
      case ApplyPredicational(_:Function, CDotFormula) => true
      case _ => false
      }, "Substitutable expression required, found " + what + " in " + this)
  }
  
  @elidable(ASSERTION) private def kindOf(e: Expr) = e match {
     case _: Term => "Term"
     case _: Formula => "Formula"
     case _: Program => "Program"
    }

  override def toString: String = "(" + what.prettyString() + "~>" + repl.prettyString() + ")"
}


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
      case ApplyPredicate(p: Function, _) => List(p)
      case Apply(f: Function, _) => List(f)
      case ApplyPredicational(p: Function, _) => List(p)
      case _ => Nil
    }).fold(Nil)((a,b) => a++b)
    require(lambdaNames.distinct.size == lambdaNames.size, "no duplicate substitutions with same substitutee modulo alpha-renaming of lambda terms " + this)
    //@TODO??? require(lambdaNames.size == subsDefs.size, "projected all replaced top-level names " + lambdaNames + " from " + this)
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
  private[core] def usubst(term: Term): Term = {
    try {
      term match {
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
        throw new SubstitutionClashException(ex.getMessage, this, term, term.prettyString()).initCause(ex)
    }
  }

  private[core] def usubst(formula: Formula): Formula = {
    log(s"Substituting ${formula.prettyString()} using $this")
    try {
      formula match {
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
        case app@ApplyPredicational(_, fml) if subsDefs.exists(sameHead(_, app)) =>
          require(admissible(SetLattice.top[NamedSymbol], fml),
            s"Substitution clash when substituting predicational ${app.prettyString()}")
          val subs = uniqueElementOf[SubstitutionPair](subsDefs, sameHead(_, app))
          val (rArg, rFormula) = (
            subs.what match { case ApplyPredicational(_, v: NamedSymbol) => v
                           case _ => throw new IllegalArgumentException(
                            s"Substitution of p(fml)=${app.prettyString()} for arbitrary fml=${fml.prettyString()} not supported")},
            subs.repl match { case f: Formula => f
                           case _ => throw new IllegalArgumentException(
                             s"Can only substitute formulas for ${app.prettyString()}")
            })
          USubst(SubstitutionPair(rArg, usubst(fml)) :: Nil).usubst(rFormula)
        case app@ApplyPredicational(q, fml) if !subsDefs.exists(sameHead(_, app)) => ApplyPredicational(q, usubst(fml))
        case True | False => formula

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
        throw new SubstitutionClashException(ex.getMessage, this, formula, formula.prettyString()).initCause(ex)
    }
  }

  // uniform substitution on programs
  private[core] def usubst(program: Program): Program = {
    try {
      program match {
        case a: ProgramConstant if subsDefs.exists(_.what == a) =>
          subsDefs.find(_.what == a).get.repl.asInstanceOf[Program]
        case a: ProgramConstant if !subsDefs.exists(_.what == a) => a
        case Assign(x: Variable, e) => Assign(x, usubst(e))
        case Assign(xp@Derivative(_, x: Variable), e) => Assign(xp, usubst(e))
        case NDetAssign(x: Variable) => NDetAssign(x)
        case Test(f) => Test(usubst(f))
        case IfThen(cond, thenT) => IfThen(usubst(cond), usubst(thenT))
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
        throw new SubstitutionClashException(ex.getMessage, this, program, program.toString()).initCause(ex)
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
        case replt: Term => sigma.what match {
          case Apply(_, Anything) => SetLattice.bottom[NamedSymbol]
          // if ever extended with f(x,y,z): StaticSemantics(t) -- {x,y,z}
          case Apply(f: Function, CDot) =>
            assert(replt == sigma.repl)
            StaticSemantics(replt) -- Set(CDot)
          case _: Term => StaticSemantics(replt)
        }
        case replf: Formula => sigma.what match {
          case ApplyPredicate(_, Anything) => SetLattice.bottom[NamedSymbol]
          // if ever extended with p(x,y,z): StaticSemantics(f) -- {x,y,z}
          case ApplyPredicate(p: Function, CDot) =>
            assert(replf == sigma.repl)
            assert(!StaticSemantics(replf).fv.contains(CDot), "CDot is no variable")
            StaticSemantics(replf).fv // equals StaticSemantics(replf).fv -- Set(CDot)
          case ApplyPredicational(ctx: Function, CDotFormula) =>
            assert(replf == sigma.repl)
            assert(!StaticSemantics(replf).fv.contains(CDotFormula), "CDotFormula is no variable")
            StaticSemantics(replf).fv
          case _: Formula => StaticSemantics(replf).fv
        }
        case replp: Program => sigma.what match {
          case _: ProgramConstant | _: DifferentialProgramConstant => SetLattice.bottom[NamedSymbol] // program constants are always admissible, since their meaning doesn't depend on state
          case _ => throw new IllegalStateException("Disallowed substitution shape " + this)
        }
      }).intersect(U) != SetLattice.bottom

    subsDefs.filter(intersectsU).flatMap(sigma => signature(sigma.what)).forall(fn => !occurrences.contains(fn))
  }

  /**
   * Check whether the function in right matches with the function in left, i.e. they have the same head.
   * @TODO Turn into more defensive algorithm that just checks head and merely asserts rather than checks that the left has the expected children.
   */
  def sameHead(left: SubstitutionPair, right: Expr) = left.what match {
    case Apply(lf, CDot | Anything | Nothing) => right match { case Apply(rf, _) => lf == rf case _ => false }
    case ApplyPredicate(lf, CDot | Anything | Nothing) => right match { case ApplyPredicate(rf, _) => lf == rf case _ => false }
    case ApplyPredicational(lf, CDotFormula) => right match { case ApplyPredicational(rf, _) => lf == rf case _ => false }
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
