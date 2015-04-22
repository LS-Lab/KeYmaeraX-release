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
import scala.collection.immutable.SortedSet
import scala.collection.immutable.Set

import scala.annotation.{unspecialized, elidable}
import scala.annotation.elidable._

import StaticSemantics._

import scala.collection.GenTraversableOnce

/**
 * Representation of a substitution replacing n with t.
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
  applicable

  import SetLattice.bottom

  @elidable(ASSERTION) def applicable = {
    require(what.kind == repl.kind,
        "substitution to same kind of expression (terms for terms, formulas for formulas, programs for programs) " + this + " substitutes " + what.kind + " ~> " + repl.kind)
    require(what.sort == repl.sort, "Sorts have to match in substitution pairs: " + what.sort + " != " + repl.sort)
    assert(what match {
     case _: Term => repl.isInstanceOf[Term]
     case _: Formula => repl.isInstanceOf[Formula]
     case _: Program => repl.isInstanceOf[Program]
    }, "(redundant test) substitution to same kind of expression (terms for terms, formulas for formulas, programs for programs) " + this + " substitutes " + what.kind + " ~> " + repl.kind)
    require(matchKey != None, "Substitutable expression required, found " + what + " in " + this) // matchKey computation did not throw exception!
  }

  /**
   * The (new) free variables of this substitution (without DotTerm/DotFormula arguments).
   * That is the (new) free variables introduced by this substitution, i.e. free variables of repl that are not bound as arguments in what.
   * @return essentially freeVars(repl) except for special handling of Anything arguments.
   */
  def freeVars : SetLattice[NamedSymbol] = (repl match {
        case replt: Term => what match {
          //case DotTerm => bottom[NamedSymbol] //@TODO eisegesis check!
          case FuncOf(f: Function, Anything) => bottom[NamedSymbol] // Anything locally binds all variables
          // if ever extended with f(x,y,z): StaticSemantics(t) -- {x,y,z}
          case FuncOf(f: Function, DotTerm) =>
            assert(replt == repl)
            assert(!StaticSemantics(replt).contains(DotTerm) || StaticSemantics(replt).isTop, "DotTerm is no variable")
            assert(!(StaticSemantics(replt) -- Set(DotTerm)).contains(DotTerm), "COMPLETENESS WARNING: removal of DotTerm from freeVars unsuccessful " + (StaticSemantics(replt) -- Set(DotTerm)) + " leading to unnecessary clashes")
            StaticSemantics(replt) -- Set(DotTerm)  // since DotTerm shouldn't be in, could be changed to StaticSemantics(replt) if lattice would know that.
          case _: Term => StaticSemantics(replt)
        }
        case replf: Formula => what match {
          //case DotFormula => bottom[NamedSymbol] //@TODO eisegesis check!
          case PredOf(p: Function, Anything) => bottom[NamedSymbol] // Anything locally binds all variables
          // if ever extended with p(x,y,z): StaticSemantics(f) -- {x,y,z}
          case PredOf(p: Function, DotTerm) =>
            assert(replf == repl)
            assert(!StaticSemantics(replf).fv.contains(DotTerm) || StaticSemantics(replf).fv.isTop, "DotTerm is no variable")
            if ((StaticSemantics(replf).fv -- Set(DotTerm)).contains(DotTerm)) println("COMPLETENESS WARNING: removal of DotTerm from freeVars unsuccessful " + (StaticSemantics(replf).fv -- Set(DotTerm)) + " leading to unnecessary clashes")
            StaticSemantics(replf).fv  -- Set(DotTerm) // since DotTerm shouldn't be in, could be changed to StaticSemantics(replf).fv if lattice would know that.
          case PredicationalOf(ctx: Function, DotFormula) =>
            assert(replf == repl)
//            assert(!StaticSemantics(replf).fv.contains(DotFormula) || StaticSemantics(replf).fv.isTop, "DotFormula is no variable")
//            if ((StaticSemantics(replf).fv -- Set(DotFormula)).contains(DotFormula)) println("COMPLETENESS WARNING: removal of DotFormula from freeVars unsuccessful " + (StaticSemantics(replf).fv -- Set(DotFormula)) + " leading to unnecessary clashes")
            bottom // predicationals are not function nor predicate symbols
            // StaticSemantics(replf).fv  -- Set(DotFormula) // since DotFormula shouldn't be in, could be changed to StaticSemantics(replf).fv if lattice would know that.
          case DotFormula => bottom // DotFormula is a nullary Predicational
          case _: Formula => StaticSemantics(replf).fv
        }
        case replp: Program => what match {
          case _: ProgramConst | _: DifferentialProgramConst => bottom[NamedSymbol] // program constants are always admissible, since their meaning doesn't depend on state
          case _ => throw new IllegalStateException("Disallowed substitution shape " + this)
        }
      })

  /**
   * The signature of the replacement introduced by this substitution.
   * @todo remove DotTerm and DotFormula arguments
   */
  def signature : Set[NamedSymbol] = StaticSemantics.signature(repl)

  /**
   * The key characteristic expression constituent that this SubstitutionPair is matching on.
   * @return only the lead / key part that this SubstitutionPair is matching on,
   *         which may not be its head.
   */
  private[core] def matchKey : NamedSymbol = what match {
    case FuncOf(f: Function, DotTerm | Nothing | Anything) => f
    case PredOf(p: Function, DotTerm | Nothing | Anything) => p
    case DotTerm => DotTerm
    case Anything => Anything
    case Nothing => assert(repl == Nothing, "can replace Nothing only by Nothing, and nothing else"); Nothing // it makes no sense to substitute Nothing
    case a: DifferentialProgramConst => a
    case a: ProgramConst => a
    case PredicationalOf(p: Function, DotFormula) => p
    case DotFormula => DotFormula
    case _ => throw new IllegalArgumentException("Nonsubstitutable expression " + this)
  }

  /**
   * Check whether we match on the term other, i.e. both have the same head.
   * @todo Turn into more defensive algorithm that just checks head and merely asserts rather than checks that the left has the expected children.
   */
  private[core] def sameHead(other: Expression) = what match {
    case FuncOf(lf, DotTerm | Anything | Nothing) => other match { case FuncOf(rf, _) => lf == rf case _ => false }
    case PredOf(lf, DotTerm | Anything | Nothing) => other match { case PredOf(rf, _) => lf == rf case _ => false }
    case PredicationalOf(lf, DotFormula) => other match { case PredicationalOf(rf, _) => lf == rf case _ => false }
    case DotTerm => other == DotTerm
    case DotFormula => other == DotFormula
    case a: DifferentialProgramConst => other == a
    case a: ProgramConst => other == a
    case _ => false
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

  import SetLattice.bottom
  import SetLattice.topVarsDiffVars

  // unique left hand sides in l
  @elidable(ASSERTION) def applicable() = {
    // check that we never replace n by something and then again replacing the same n by something
    val lefts = subsDefs.map(_.what).toList
    require(lefts.distinct.size == lefts.size, "no duplicate substitutions with same substitutees " + subsDefs)
    // check that we never replace p(x) by something and also p(t) by something
    val lambdaNames = matchKeys
    require(lambdaNames.distinct.size == lambdaNames.size, "no duplicate substitutions with same substitutee modulo alpha-renaming of lambda terms " + this)
  }

  @elidable(FINEST-1) private def log(msg: =>String) {}  //= println(msg)

  override def toString: String = "USubst(" + subsDefs.mkString(", ") + ")"

  def apply(t: Term): Term = usubst(t) ensuring(
    r => matchKeys.toSet.intersect(StaticSemantics.signature(r)--signature).isEmpty, "Uniform Substitution substituted all occurrences (except when reintroduced by substitution) " + this + "\non" + t + "\ngave " + usubst(t))
  def apply(f: Formula): Formula = usubst(f) ensuring(
    r => matchKeys.toSet.intersect(StaticSemantics.signature(r)--signature).isEmpty, "Uniform Substitution substituted all occurrences (except when reintroduced by substitution) " + this + "\non" + f + "\ngave " + usubst(f))
  def apply(p: Program): Program = usubst(p) ensuring(
    r => matchKeys.toSet.intersect(StaticSemantics.signature(r)--signature).isEmpty, "Uniform Substitution substituted all occurrences (except when reintroduced by substitution) " + this + "\non" + p + "\ngave " + usubst(p))

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
   * The (new) free variables of this substitution (without DotTerm/DotFormula arguments).
   * That is the (new) free variables introduced by this substitution, i.e.
   * free variables of all repl that are not bound as arguments in what.
   * @return union of the freeVars of all our substitution pairs.
   */
  def freeVars : SetLattice[NamedSymbol] = {
    subsDefs.foldLeft(bottom[NamedSymbol])((a,b)=>a ++ (b.freeVars))
  } ensuring(r => r == subsDefs.map(_.freeVars).
      foldLeft(bottom[NamedSymbol])((a,b)=>a++b), "free variables identical, whether computed with map or with fold")

  /**
   * The signature of the replacement introduced by this substitution.
   * @return union of the freeVars of all our substitution pairs.
   */
  def signature : Set[NamedSymbol] = {
    subsDefs.foldLeft(Set.empty[NamedSymbol])((a,b)=>a ++ (b.signature))
  } ensuring(r => r == subsDefs.map(_.signature).
    foldLeft(Set.empty[NamedSymbol])((a,b)=>a++b), "signature identical, whether computed with map or with fold")

  /**
   * The key characteristic expression constituents that this Substitution is matching on.
   * @return union of the matchKeys of all our substitution pairs.
   */
  def matchKeys : List[NamedSymbol] = {
    subsDefs.foldLeft(List[NamedSymbol]())((a,b)=>a ++ List(b.matchKey))
  }

  /**
   * Whether this substitution matches to replace the given expression e.
   */
  private def matchHead(e: Expression) : Boolean = subsDefs.exists(sp => sp.sameHead(e))


  // implementation of uniform substitution application
      
  // uniform substitution on terms
  private[core] def usubst(term: Term): Term = {
    try {
      term match {
        // uniform substitution base cases
        case x: Variable => assert(!subsDefs.exists(_.what == x), "Substitution of variables not supported: " + x); x
        case xp@DifferentialSymbol(x: Variable) => assert(!subsDefs.exists(_.what == xp),
          "Substitution of differential symbols not supported: " + xp); xp
        case app@FuncOf(_:Function, theta) if matchHead(app) =>
          val subs = uniqueElementOf[SubstitutionPair](subsDefs, _.sameHead(app))
          val (rArg, rTerm) =
            (subs.what match { case FuncOf(_:Function, v: NamedSymbol) => v
                            case _ => throw new IllegalArgumentException(
                              "Substitution of f(" + theta.prettyString() + ")=" + app.prettyString() + " not supported for arbitrary argument " + theta) },
             subs.repl match { case t: Term => t
                            case _ => throw new IllegalArgumentException(
                              "Can only substitute terms for " + app.prettyString())}
            )
          USubst(SubstitutionPair(rArg, usubst(theta)) :: Nil).usubst(rTerm)
        case app@FuncOf(g:Function, theta) if !matchHead(app) => FuncOf(g, usubst(theta))
        case Anything => assert(!subsDefs.exists(_.what == Anything)); Anything // TODO check
        case Nothing => {
          assert(!subsDefs.exists(sp => sp.what == Nothing && sp.repl != Nothing), "can replace Nothing only by Nothing, and nothing else");
          Nothing
        }
        case DotTerm if  subsDefs.exists(_.what == DotTerm) => // TODO check (should be case x = sigma x for variable x)
          subsDefs.find(_.what == DotTerm).get.repl match {
            case t: Term => t
            case _ => throw new IllegalArgumentException("Can only substitute terms for " + DotTerm)
          }
        case DotTerm if !subsDefs.exists(_.what == DotTerm) => DotTerm // TODO check (should be case x = sigma x for variable x)
        case n: Number => n
        //@TODO any way of ensuring for the following that top-level(t)==top-level(\result)
         // homomorphic cases
        case Neg(e) => Neg(usubst(e))
        case Plus(l, r) => Plus(usubst(l), usubst(r))
        case Minus(l, r) => Minus(usubst(l), usubst(r))
        case Times(l, r) => Times(usubst(l), usubst(r))
        case Divide(l, r) => Divide(usubst(l), usubst(r))
        case Power(l, r) => Power(usubst(l), usubst(r))
        case der@Differential(e) =>
          require(admissible(topVarsDiffVars[NamedSymbol], e),
            "Substitution clash when substituting " + this + " in derivative " + der.prettyString() + " FV(" + e + ") = " + StaticSemantics(e).prettyString + " is not empty")
          Differential(usubst(e))
        // unofficial
        case Pair(l, r) => Pair(usubst(l), usubst(r))  
      }
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this.toString, term.prettyString()).initCause(ex)
    }
  } ensuring(
    r => r.kind == term.kind && r.sort == term.sort, "Uniform Substitution leads to same kind and same sort " + term)

  private[core] def usubst(formula: Formula): Formula = {
    log(s"Substituting ${formula.prettyString()} using $this")
    try {
      formula match {
        case app@PredOf(_, theta) if matchHead(app) =>
          val subs = uniqueElementOf[SubstitutionPair](subsDefs, _.sameHead(app))
          val (rArg, rFormula) = (
            subs.what match { case PredOf(_, v: NamedSymbol) => v
                           case _ => throw new IllegalArgumentException(
                            s"Substitution of p(theta)=${app.prettyString()} for arbitrary theta=${theta.prettyString()} not supported")},
            subs.repl match { case f: Formula => f
                           case _ => throw new IllegalArgumentException(
                             s"Can only substitute formulas for ${app.prettyString()}")
            })
          USubst(SubstitutionPair(rArg, usubst(theta)) :: Nil).usubst(rFormula)
        case app@PredOf(q, theta) if !matchHead(app) => PredOf(q, usubst(theta))
        case app@PredicationalOf(_, fml) if matchHead(app) =>
          require(admissible(topVarsDiffVars[NamedSymbol], fml),
            "Substitution clash when substituting " + this + " in predicational " +  app.prettyString() + " FV(" + fml + ") = " + StaticSemantics(fml).fv.prettyString + " is not empty")
          val subs = uniqueElementOf[SubstitutionPair](subsDefs, _.sameHead(app))
          val (rArg, rFormula) = (
            subs.what match { case PredicationalOf(_, v: NamedSymbol) => v
                           case _ => throw new IllegalArgumentException(
                            s"Substitution of p(fml)=${app.prettyString()} for arbitrary fml=${fml.prettyString()} not supported")},
            subs.repl match { case f: Formula => f
                           case _ => throw new IllegalArgumentException(
                             s"Can only substitute formulas for ${app.prettyString()}")
            })
          USubst(SubstitutionPair(rArg, usubst(fml)) :: Nil).usubst(rFormula)
        case app@PredicationalOf(q, fml) if !matchHead(app) => PredicationalOf(q, usubst(fml))
        case DotFormula if !subsDefs.exists(_.what == DotFormula) => DotFormula // TODO check (should be case x = sigma x for variable x)
        case DotFormula if  subsDefs.exists(_.what == DotFormula) => // TODO check (should be case x = sigma x for variable x)
          subsDefs.find(_.what == DotFormula).get.repl match {
            case f: Formula => f
            case _ => throw new IllegalArgumentException("Can only substitute formulas for " + DotFormula)
          }
        case True | False => formula

        //@TODO any way of ensuring for the following that  top-level(f)==top-level(\result)
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

        case der@DifferentialFormula(g) =>
          require(admissible(topVarsDiffVars[NamedSymbol], g),
            "Substitution clash when substituting " + this + " in derivative " +  der.prettyString() + ": FV(" + g + ") = " + StaticSemantics(g).fv.prettyString + " is not empty")
          DifferentialFormula(usubst(g))

        // binding cases add bound variables to u
        case Forall(vars, g) => require(admissible(SetLattice(vars).toSetLattice[NamedSymbol], g),
          "Substitution clash: " + this + " not " + vars.mkString(",") + "-admissible for " + g.prettyString() + " when substituting in " + formula.prettyString())
            Forall(vars, usubst(g))
        case Exists(vars, g) => require(admissible(SetLattice(vars).toSetLattice[NamedSymbol], g),
          "Substitution clash: " + this + " not " + vars.mkString(",") + "-admissible for " + g.prettyString() + " when substituting in " + formula.prettyString())
            Exists(vars, usubst(g))

        case Box(p, g) => require(admissible(StaticSemantics(usubst(p)).bv, g),
          "Substitution clash:" + this + " not " + StaticSemantics(usubst(p)).bv.prettyString + "-admissible for " + g.prettyString() + " when substituting in " + formula.prettyString())
            Box(usubst(p), usubst(g))
        case Diamond(p, g) => require(admissible(StaticSemantics(usubst(p)).bv, g),
          "Substitution clash:" + this + " not " +  StaticSemantics(usubst(p)).bv.prettyString + "-admissible for " + g.prettyString() + " when substituting in " + formula.prettyString())
            Diamond(usubst(p), usubst(g))
      }
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this.toString, formula.prettyString()).initCause(ex)
    }
  } ensuring(
    r => r.kind == formula.kind && r.sort == formula.sort, "Uniform Substitution leads to same kind and same sort " + formula)

  // uniform substitution on programs
  private[core] def usubst(program: Program): Program = {
    try {
      program match {
        case a: ProgramConst if subsDefs.exists(_.what == a) =>
          subsDefs.find(_.what == a).get.repl.asInstanceOf[Program]
        case a: ProgramConst if !subsDefs.exists(_.what == a) => a
        case Assign(x: Variable, e) => Assign(x, usubst(e))
        case DiffAssign(xp:DifferentialSymbol, e) => DiffAssign(xp, usubst(e))
        case a: AssignAny => a
        case Test(f) => Test(usubst(f))
        //case IfThen(cond, thenT) => IfThen(usubst(cond), usubst(thenT))
        case ode: DifferentialProgram =>
          // require is redundant with the checks on NFContEvolve in usubst(ode, primed)
          require(admissible(StaticSemantics(ode).bv, ode),
          "Substitution clash: " + this + " not " + StaticSemantics(ode).bv.prettyString + "-admissible when substituting in " + program.prettyString)
          usubstODE(ode, StaticSemantics(ode).bv)
        case Choice(a, b) => Choice(usubst(a), usubst(b))
        case Compose(a, b) => require(admissible(StaticSemantics(usubst(a)).bv, b),
          "Substitution clash: " + this + " not " + StaticSemantics(usubst(a)).bv.prettyString + "-admissible for " + b.prettyString() + " when substituting in " + program.prettyString())
          Compose(usubst(a), usubst(b))
        case Loop(a) => require(admissible(StaticSemantics(usubst(a)).bv, a),
          "Substitution clash: " + this + " not " + StaticSemantics(usubst(a)).bv.prettyString + "-admissible for " + a.prettyString() + " when substituting in " + program.prettyString())
          Loop(usubst(a))
      }
    } catch {
      case ex: IllegalArgumentException =>
        throw new SubstitutionClashException(ex.getMessage, this.toString, program.toString()).initCause(ex)
    }
  } ensuring(
    r => r.kind == program.kind && r.sort == program.sort, "Uniform Substitution leads to same kind and same sort " + program)

  private def usubstODE(ode: DifferentialProgram, primed: SetLattice[NamedSymbol]): DifferentialProgram = {
    ode match {
      case ODESystem(a, h) =>
        require(admissible(primed, h), "Substitution clash in ODE: {x}=" + primed + " clash with " + h.prettyString())
        ODESystem(usubstODE(a, primed), usubst(h))
      case AtomicODE(xp: DifferentialSymbol, t) =>
        require(admissible(primed, t),
          "Substitution clash: " + this + " not " + primed + "-admissible for " + t.prettyString() + " when substituting in " + ode.prettyString())
        AtomicODE(xp, usubst(t))
      case DifferentialProduct(a, b) => DifferentialProduct(usubstODE(a, primed), usubstODE(b, primed))
      case c: DifferentialProgramConst if subsDefs.exists(_.what == c) =>
        val repl = subsDefs.find(_.what == c).get.repl
        repl match {
          case replODE: DifferentialProgram => replODE
          case _ => throw new IllegalArgumentException("Can only substitute continuous programs for " +
            "continuous program constants: " + repl + " not allowed for " + c)
        }
      case c: DifferentialProgramConst if !subsDefs.exists(_.what == c) => c
    }
  } ensuring(
    r => r.kind == ode.kind && r.sort == ode.sort, "Uniform Substitution leads to same kind and same sort " + ode)

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
        sigma.freeVars.intersect(U) != bottom

    subsDefs.filter(intersectsU).flatMap(sigma => StaticSemantics.signature(sigma.what)).forall(fn => !occurrences.contains(fn))
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
    require(c.count(pred) == 1, "unique element expected in " + c.mkString)
    c.filter(pred).head
  }
}
