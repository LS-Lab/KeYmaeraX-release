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
      case Nothing => repl == Nothing
      case Apply(_:Function, CDot | Nothing | Anything) => true
      case ApplyPredicate(_:Function, CDot | Nothing | Anything) => true
      case _:ProgramConstant => true
      case _:DifferentialProgramConstant => true
      case CDotFormula => true
      case ApplyPredicational(_:Function, CDotFormula) => true
      case xp@Derivative(Real, x: Variable) => require(false,
        "Substitution of differential symbols not supported: " + xp); false
      case _ => false
      }, "Substitutable expression required, found " + what + " in " + this)
  }

  /**
   * The key characteristic expression constituent that this SubstitutionPair is matching on.
   * @return only the lead / key part that this SubstitutionPair is matching on,
   *         which may not be its head.
   */
  private[core] def matchKey : NamedSymbol = what match {
    case CDot => CDot
    case Anything => Anything
    case a: ProgramConstant => a
    case a: DifferentialProgramConstant => a
    case Apply(f: Function, CDot | Nothing | Anything) => f
    case ApplyPredicate(p: Function, CDot | Nothing | Anything) => p
    case Nothing => Nothing
    case CDotFormula => CDotFormula
    case ApplyPredicational(p: Function, CDotFormula) => p
  }

  /**
   * Check whether the function in right matches with the function in left, i.e. they have the same head.
   * @TODO Turn into more defensive algorithm that just checks head and merely asserts rather than checks that the left has the expected children.
   */
  private[core] def sameHead(right: Expr) = what match {
    case Apply(lf, CDot | Anything | Nothing) => right match { case Apply(rf, _) => lf == rf case _ => false }
    case ApplyPredicate(lf, CDot | Anything | Nothing) => right match { case ApplyPredicate(rf, _) => lf == rf case _ => false }
    case ApplyPredicational(lf, CDotFormula) => right match { case ApplyPredicational(rf, _) => lf == rf case _ => false }
    case _ => false
  }

  //@TODO Isn't there a better way of doing this?
  @elidable(ASSERTION) private def kindOf(e: Expr) = e match {
     case _: Term => "Term"
     case _: Formula => "Formula"
     case _: Program => "Program"
    }

  /**
   * The (new) free variables of this substitution (without CDot/CDotFormula arguments).
   * That is the (new) free variables introduced by this substitution, i.e. free variables of repl that are not bound as arguments in what.
   * @return essentially freeVars(repl) except for special handling of Anything arguments.
   */
  def freeVars : SetLattice[NamedSymbol] = (repl match {
        case replt: Term => what match {
          //case CDot => SetLattice.bottom[NamedSymbol] //@TODO eisegesis check!
          case Apply(f: Function, Anything) => SetLattice.bottom[NamedSymbol] // Anything locally binds all variables
          // if ever extended with f(x,y,z): StaticSemantics(t) -- {x,y,z}
          case Apply(f: Function, CDot) =>
            assert(replt == repl)
            assert(!StaticSemantics(replt).contains(CDot) || StaticSemantics(replt).isTop, "CDot is no variable")
            if ((StaticSemantics(replt) -- Set(CDot)).contains(CDot)) println("COMPLETENESS WARNING: removal of CDot from freeVars unsuccessful " + (StaticSemantics(replt) -- Set(CDot)) + " leading to unnecessary clashes")
            StaticSemantics(replt) -- Set(CDot)  // since CDot shouldn't be in, could be changed to StaticSemantics(replt) if lattice would know that.
          case _: Term => StaticSemantics(replt)
        }
        case replf: Formula => what match {
          //case CDotFormula => SetLattice.bottom[NamedSymbol] //@TODO eisegesis check!
          case ApplyPredicate(_, Anything) => SetLattice.bottom[NamedSymbol] // Anything locally binds all variables
          // if ever extended with p(x,y,z): StaticSemantics(f) -- {x,y,z}
          case ApplyPredicate(p: Function, CDot) =>
            assert(replf == repl)
            assert(!StaticSemantics(replf).fv.contains(CDot) || StaticSemantics(replf).fv.isTop, "CDot is no variable")
            if ((StaticSemantics(replf).fv -- Set(CDot)).contains(CDot)) println("COMPLETENESS WARNING: removal of CDot from freeVars unsuccessful " + (StaticSemantics(replf).fv -- Set(CDot)) + " leading to unnecessary clashes")
            StaticSemantics(replf).fv  -- Set(CDot) // since CDot shouldn't be in, could be changed to StaticSemantics(replf).fv if lattice would know that.
          case ApplyPredicational(ctx: Function, CDotFormula) =>
            assert(replf == repl)
            assert(!StaticSemantics(replf).fv.contains(CDotFormula) || StaticSemantics(replf).fv.isTop, "CDotFormula is no variable")
            if ((StaticSemantics(replf).fv -- Set(CDotFormula)).contains(CDotFormula)) println("COMPLETENESS WARNING: removal of CDotFormula from freeVars unsuccessful " + (StaticSemantics(replf).fv -- Set(CDotFormula)) + " leading to unnecessary clashes")
            SetLattice.bottom // predicationals are not function nor predicate symbols
            // StaticSemantics(replf).fv  -- Set(CDotFormula) // since CDotFormula shouldn't be in, could be changed to StaticSemantics(replf).fv if lattice would know that.
          case CDotFormula => SetLattice.bottom // CDotFormula is a nullary Predicational
          case _: Formula => StaticSemantics(replf).fv
        }
        case replp: Program => what match {
          case _: ProgramConstant | _: DifferentialProgramConstant => SetLattice.bottom[NamedSymbol] // program constants are always admissible, since their meaning doesn't depend on state
          case _ => throw new IllegalStateException("Disallowed substitution shape " + this)
        }
      })

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
  }

  @elidable(FINEST-1) private def log(msg: =>String) {}  //= println(msg)

  override def toString: String = "USubst(" + subsDefs.mkString(", ") + ")"

  def apply(t: Term): Term = usubst(t)
  def apply(f: Formula): Formula = usubst(f)
  def apply(p: Program): Program = usubst(p)

//  /**
//   * Cross-check with FastUSubst
//   */
//  private val nocheck: Boolean = true
//  def apply(t: Term): Term = {
//    usubst(t)
//  } ensuring(nocheck || _ == new FastUSubst(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], t),
//    s"USubst result ${usubst(t)} does not agree with fast result " +
//      s"${new FastUSubst(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], t)}")
//  def apply(f: Formula): Formula = {
//    usubst(f)
//  } ensuring(nocheck || _ == new FastUSubst(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], f),
//    s"USubst result ${usubst(f)} does not agree with fast result " +
//      s"${new FastUSubst(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], f)}")
//  def apply(p: Program): Program = {
//    usubst(p)
//  } ensuring(nocheck || _ == new FastUSubst(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], p).p,
//    s"USubst result ${usubst(p)} does not agree with fast result " +
//      s"${new FastUSubst(subsDefs).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], p)}")

  /**
   * Apply uniform substitution everywhere in the sequent.
   */
  def apply(s: Sequent): Sequent = {
    try {
      Sequent(s.pref, s.ante.map(apply), s.succ.map(apply))
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this.toString, s.toString()).initCause(ex)
    }
  }

  /**
   * The (new) free variables of this substitution (without CDot/CDotFormula arguments).
   * That is the (new) free variables introduced by this substitution, i.e.
   * free variables of all repl that are not bound as arguments in what.
   * @return union of the freeVars of all our substitution pairs.
   */
  def freeVars : SetLattice[NamedSymbol] = subsDefs.map(_.freeVars).
    foldLeft(SetLattice.bottom[NamedSymbol])((a,b)=>a++b)

  // implementation of uniform substitution application
      
  // uniform substitution on terms
  private[core] def usubst(term: Term): Term = {
    try {
      term match {
        // uniform substitution base cases
        case x: Variable => require(!subsDefs.exists(_.what == x), "Substitution of variables not supported: " + x); x
        case xp@Derivative(Real, x: Variable) => require(!subsDefs.exists(_.what == xp),
          "Substitution of differential symbols not supported: " + xp); xp
        case app@Apply(_, theta) if subsDefs.exists(_.sameHead(app)) =>
          val subs = uniqueElementOf[SubstitutionPair](subsDefs, _.sameHead(app))
          val (rArg, rTerm) =
            (subs.what match { case Apply(_, v: NamedSymbol) => v
                            case _ => throw new IllegalArgumentException(
                              "Substitution of f(" + theta.prettyString() + ")=" + app.prettyString() + " not supported for arbitrary argument " + theta) },
             subs.repl match { case t: Term => t
                            case _ => throw new IllegalArgumentException(
                              "Can only substitute terms for " + app.prettyString())}
            )
          USubst(SubstitutionPair(rArg, usubst(theta)) :: Nil).usubst(rTerm)
        case app@Apply(g, theta) if !subsDefs.exists(_.sameHead(app)) => Apply(g, usubst(theta))
        case Anything => Anything // TODO check
        case Nothing => Nothing // TODO check
        case CDot if !subsDefs.exists(_.what == CDot) => CDot // TODO check (should be case x = sigma x for variable x)
        case CDot if  subsDefs.exists(_.what == CDot) => // TODO check (should be case x = sigma x for variable x)
          subsDefs.find(_.what == CDot).get.repl match {
            case t: Term => t
            case _ => throw new IllegalArgumentException("Can only substitute terms for " + CDot)
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
            "Substitution clash when substituting " + this + " in derivative " + der.prettyString() + " FV(" + e + ") = " + StaticSemantics(e).prettyString + " is not empty")
          Derivative(Real, usubst(e))
      }
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this.toString, term.prettyString()).initCause(ex)
    }
  }

  private[core] def usubst(formula: Formula): Formula = {
    log(s"Substituting ${formula.prettyString()} using $this")
    try {
      formula match {
        case app@ApplyPredicate(_, theta) if subsDefs.exists(_.sameHead(app)) =>
          val subs = uniqueElementOf[SubstitutionPair](subsDefs, _.sameHead(app))
          val (rArg, rFormula) = (
            subs.what match { case ApplyPredicate(_, v: NamedSymbol) => v
                           case _ => throw new IllegalArgumentException(
                            s"Substitution of p(theta)=${app.prettyString()} for arbitrary theta=${theta.prettyString()} not supported")},
            subs.repl match { case f: Formula => f
                           case _ => throw new IllegalArgumentException(
                             s"Can only substitute formulas for ${app.prettyString()}")
            })
          USubst(SubstitutionPair(rArg, usubst(theta)) :: Nil).usubst(rFormula)
        case app@ApplyPredicate(q, theta) if !subsDefs.exists(_.sameHead(app)) => ApplyPredicate(q, usubst(theta))
        case app@ApplyPredicational(_, fml) if subsDefs.exists(_.sameHead(app)) =>
          require(admissible(SetLattice.top[NamedSymbol], fml),
            "Substitution clash when substituting " + this + " in predicational " +  app.prettyString() + " FV(" + fml + ") = " + StaticSemantics(fml).fv.prettyString + " is not empty")
          val subs = uniqueElementOf[SubstitutionPair](subsDefs, _.sameHead(app))
          val (rArg, rFormula) = (
            subs.what match { case ApplyPredicational(_, v: NamedSymbol) => v
                           case _ => throw new IllegalArgumentException(
                            s"Substitution of p(fml)=${app.prettyString()} for arbitrary fml=${fml.prettyString()} not supported")},
            subs.repl match { case f: Formula => f
                           case _ => throw new IllegalArgumentException(
                             s"Can only substitute formulas for ${app.prettyString()}")
            })
          USubst(SubstitutionPair(rArg, usubst(fml)) :: Nil).usubst(rFormula)
        case app@ApplyPredicational(q, fml) if !subsDefs.exists(_.sameHead(app)) => ApplyPredicational(q, usubst(fml))
        case CDotFormula if !subsDefs.exists(_.what == CDotFormula) => CDotFormula // TODO check (should be case x = sigma x for variable x)
        case CDotFormula if  subsDefs.exists(_.what == CDotFormula) => // TODO check (should be case x = sigma x for variable x)
          subsDefs.find(_.what == CDotFormula).get.repl match {
            case f: Formula => f
            case _ => throw new IllegalArgumentException("Can only substitute formulas for " + CDotFormula)
          }
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
            "Substitution clash when substituting " + this + " in derivative " +  der.prettyString() + ": FV(" + g + ") = " + StaticSemantics(g).fv.prettyString + " is not empty")
          FormulaDerivative(usubst(g))

        // binding cases add bound variables to u
        case Forall(vars, g) => require(admissible(SetLattice(vars), g),
          "Substitution clash: " + this + " not " + vars.mkString(",") + "-admissible for " + g.prettyString() + " when substituting in " + formula.prettyString())
            Forall(vars, usubst(g))
        case Exists(vars, g) => require(admissible(SetLattice(vars), g),
          "Substitution clash: " + this + " not " + vars.mkString(",") + "-admissible for " + g.prettyString() + " when substituting in " + formula.prettyString())
            Exists(vars, usubst(g))

        case BoxModality(p, g) => require(admissible(StaticSemantics(usubst(p)).bv, g),
          "Substitution clash:" + this + " not " + StaticSemantics(usubst(p)).bv.prettyString + "-admissible for " + g.prettyString() + " when substituting in " + formula.prettyString())
            BoxModality(usubst(p), usubst(g))
        case DiamondModality(p, g) => require(admissible(StaticSemantics(usubst(p)).bv, g),
          "Substitution clash:" + this + " not " +  StaticSemantics(usubst(p)).bv.prettyString + "-admissible for " + g.prettyString() + " when substituting in " + formula.prettyString())
            DiamondModality(usubst(p), usubst(g))
      }
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this.toString, formula.prettyString()).initCause(ex)
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
          "Substitution clash: " + this + " not " + StaticSemantics(ode).bv.prettyString + "-admissible when substituting in " + program.prettyString)
          usubstODE(ode, StaticSemantics(ode).bv)
        case Choice(a, b) => Choice(usubst(a), usubst(b))
        case Sequence(a, b) => require(admissible(StaticSemantics(usubst(a)).bv, b),
          "Substitution clash: " + this + " not " + StaticSemantics(usubst(a)).bv.prettyString + "-admissible for " + b.prettyString() + " when substituting in " + program.prettyString())
          Sequence(usubst(a), usubst(b))
        case Loop(a) => require(admissible(StaticSemantics(usubst(a)).bv, a),
          "Substitution clash: " + this + " not " + StaticSemantics(usubst(a)).bv.prettyString + "-admissible for " + a.prettyString() + " when substituting in " + program.prettyString())
          Loop(usubst(a))
      }
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this.toString, program.toString()).initCause(ex)
    }
  }

  private def usubstODE(ode: DifferentialProgram, primed: SetLattice[NamedSymbol]): DifferentialProgram = ode match {
    case ODESystem(d, a, h) if d.isEmpty =>
      require(admissible(primed, h), s"Substitution clash in ODE: {x}=$primed clash with ${h.prettyString()}")
      ODESystem(d, usubstODE(a, primed), usubst(h))
    case ODESystem(d, a , h) if d.nonEmpty => throw new UnknownOperatorException("Check implementation whether passing v is correct.", ode)
    case AtomicODE(dv: Derivative, t) =>
      require(admissible(primed, t),
      s"Substitution clash: ${this} not {$primed}-admissible for {$t.prettyString()} when substituting in ${ode.prettyString()}")
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
   * @param U taboo list of variables
   * @param occurrences the function and predicate symbols occurring in the expression of interest.
   */
  private def admissible(U: SetLattice[NamedSymbol], occurrences: Set[NamedSymbol]) : Boolean = {
      // if  no function symbol f in sigma with FV(sigma f(.)) /\ U != empty
      // and no predicate symbol p in sigma with FV(sigma p(.)) /\ U != empty
      // occurs in theta (or phi or alpha)
      def intersectsU(sigma: SubstitutionPair): Boolean =
        sigma.freeVars.intersect(U) != SetLattice.bottom

    subsDefs.filter(intersectsU).flatMap(sigma => signature(sigma.what)).forall(fn => !occurrences.contains(fn))
  } ensuring(r =>
    // U-admissible iff FV(restrict sigma to occurrences) /\ U = empty
    r == projection(occurrences).freeVars.intersect(U).isEmpty,
    this + " is " + U + "-admissible iff restriction " + projection(occurrences) + " to occurring symbols " + occurrences + " has no free variables " + projection(occurrences).freeVars + " of " + U)

  /**
   * Projects a substitution to only those that affect the symbols listed in occurrences.
   */
  private def projection(affected: Set[NamedSymbol]) : USubst = new USubst(
    subsDefs.filter(sigma => affected.contains(sigma.matchKey))
  )

  /**
   * Get the unique element in c to which pred applies.
   * Protests if that element is not unique because pred applies to more than one element in c or if there is none.
   */
  private def uniqueElementOf[E](c: Iterable[E], pred: E => Boolean): E = {
    require(c.count(pred) == 1, "unique element expected in {$c.mkString}")
    c.filter(pred).head
  }
}
