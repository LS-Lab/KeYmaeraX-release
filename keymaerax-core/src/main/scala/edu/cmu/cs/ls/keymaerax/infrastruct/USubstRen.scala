/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.core.SetLattice._
import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable
import scala.collection.immutable._

object USubstRenChurch {
  /** `true` for transpositions (replace `what` by `repl` and `what'` by `repl'` and, vice versa, `repl` by `what` etc) or `false` to clash upon occurrences of `repl` or `repl'`. */
  private[infrastruct] val TRANSPOSITION: Boolean = URename(Variable("dummy"),Variable("ymmud"))(Variable("ymmud"))==Variable("dummy")
}

/**
  * Standalone Renaming Uniform Substitution operation, simultaneously combining [[URename]] and [[USubst]].
  * This implementation uses Church-style uniform substitution implementation a la [[USubstChurch]].
  * Liberal list of SubstitutionPair represented as merely a list of Pair,
  * where the Variable~>Variable replacements are by uniform renaming,
  * and the other replacements are by uniform substitution, simultaneously.
  *
  * @note This implementation performs semantic renaming.
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.core.URename]]
  * @see [[edu.cmu.cs.ls.keymaerax.core.USubstChurch]]
  * @see [[MultiRename]]
  * @see [[USubstRenOne]]
  */
//@todo admissibility needs to be augmented with renamed variables too for soundness.
//@todo does not check soundness-critical occurrence constraints for Taboos, but the core ultimately will.
final case class USubstRenChurch(private[infrastruct] val subsDefsInput: immutable.Seq[(Expression,Expression)]) extends (Expression => Expression) {
  insist(subsDefsInput.forall(sp => sp._1.kind == sp._2.kind), "Substitution renaming only to expressions of the same kind: " + this)
  insist(subsDefsInput.forall(sp => sp._1.sort == sp._2.sort), "Substitution renaming only to expressions of the same sort: " + this)
  insist({val repls = subsDefsInput.map(sp=>sp._1).toList; repls.length == repls.distinct.length}, "No contradictory or duplicate substitutions/renamings: " + this)

  /** substitution part */
  private val subs: immutable.Map[Expression,Expression] = subsDefsInput.filter(sp => !sp._1.isInstanceOf[Variable]).toMap
  /** renaming part, augmented with transpositions */
  private val rens: immutable.Map[Variable,Variable] = augmentTranspositions(RenUSubst.renamingPartOnly(subsDefsInput).toMap)

  /** include transpositions for renamings if need be */
  private def augmentTranspositions(rena: immutable.Map[Variable,Variable]): immutable.Map[Variable,Variable] = {
    insist(rena.keySet.intersect(rena.values.toSet).isEmpty, "No replacement of a variable should be renamed in cyclic ways again: " + this)
      rena ++ (rena.map(sp => sp._2->sp._1))
  } ensures( r => rena.forall(sp => r.get(sp._1)==Some(sp._2) && r.get(sp._2)==Some(sp._1)), "converse renamings are contained for " + rena)

  /** the ApplicationOf subset of subs with matching heads */
  private val matchHeads: immutable.Map[Function,(ApplicationOf,Expression)] =
    subs.filter(sp => sp._1.isInstanceOf[ApplicationOf]).map(
      sp => {
        val app = sp._1.asInstanceOf[ApplicationOf]
        (app.func, (app, sp._2))
      })

  //if (BelleExpr.DEBUG) println("DOING " + this + "  with  rens=" + rens.map(sp => sp._1.prettyString + "~~>" + sp._2.prettyString).mkString(",") + "  subs=" + subs.map(sp => sp._1.prettyString + "~>" + sp._2.prettyString).mkString(",") + "  heads=" + matchHeads)

  //@todo check for substitutable expressions like in USubst

  override def toString: String = "USubstRen{" + subsDefsInput.map(sp => sp._1.prettyString + "~>" + sp._2.prettyString).mkString(", ") + "}"


  /** This USubstRen implemented strictly from the core. */
  val toCore: Expression => Expression = e => {
    val renall = MultiRename(RenUSubst.renamingPartOnly(subsDefsInput))
    // rename all substitutions (by transposition) since they'll be renamed back subsequently
    val usubst = USubstChurch(subs.toList.map(sp => SubstitutionPair(sp._1, renall(sp._2))))
    val replaced = usubst(e)
    renall.toCore(replaced)
  }

  /**
    * The (new) free variables that this substitution introduces (without DotTerm/DotFormula arguments).
    * That is the (new) free variables introduced by this substitution, i.e.
    * free variables of all repl that are not bound as arguments in what.
    * @return union of the freeVars of all our substitution pairs.
    */
  def freeVars: SetLattice[Variable] = {
    matchHeads.foldLeft(bottom[Variable])((a,b) => a ++ StaticSemantics.freeVars(b._2._2))
  }

  /** apply this uniform renaming everywhere in an expression, resulting in an expression of the same kind. */
  def apply(e: Expression): Expression = e match {
    case t: Term => apply(t)
    case f: Formula => apply(f)
    case p: DifferentialProgram => apply(p)
    case p: Program => apply(p)
    case f: Function => throw new SubstitutionClashException(toString, "", e.toString, "", "", "substitutions are not defined on an isolated Function that is not applied to arguments.")
  }

  /** apply this uniform substitution renaming everywhere in a term */
  def apply(t: Term): Term = try usubst(t) catch { case ex: ProverException => throw ex.inContext(t.prettyString) }

  /** apply this uniform substitution renaming everywhere in a formula */
  def apply(f: Formula): Formula = try usubst(f) catch { case ex: ProverException => throw ex.inContext(f.prettyString) }

  /** apply this uniform substitution renaming everywhere in a program */
  def apply(p: DifferentialProgram): DifferentialProgram = try usubst(p) catch { case ex: ProverException => throw ex.inContext(p.prettyString) }

  /** apply this uniform substitution renaming everywhere in a program */
  def apply(p: Program): Program = try usubst(p) catch { case ex: ProverException => throw ex.inContext(p.prettyString) }

  /**
   * Apply uniform substitution renaming everywhere in the sequent.
   */
  //@note mapping apply instead of the equivalent rename makes sure the exceptions are augmented and the ensures contracts checked.
  def apply(s: Sequent): Sequent = try { Sequent(s.ante.map(apply), s.succ.map(apply))
  } catch { case ex: ProverException => throw ex.inContext(s.toString) }


  // implementation

  /**
    * Whether this substitution matches to replace the given expression e,
    * because there is a substitution pair that matches e.
    */
  private def matchHead(e: ApplicationOf): Boolean = matchHeads.contains(e.func)

  /** Rename a variable (that occurs in the given context for error reporting purposes) */
  private def renameVar(x: Variable, context: Expression): Variable = rens.get(x) match {
    case Some(repl) => repl
    case None => x match {
      case DifferentialSymbol(y) => DifferentialSymbol(renameVar(y, context))
      case _ => x
    }
  }

  // implementation of uniform substitution application
      
  /** uniform substitution on terms */
  private def usubst(term: Term): Term = {
    term match {
      // uniform substitution base cases
      case x: Variable => renameVar(x, term)
//      case DifferentialSymbol(x) => DifferentialSymbol(renameVar(x, term))
      case app@FuncOf(of, theta) if matchHead(app) =>
        val (what, repl) = matchHeads(of)
        val FuncOf(wf, wArg) = what
        assert(wf == of, "match on same function heads")
        assert(isDot(wArg) || wArg == Nothing)
        // unofficial substitution for Nothing (no effect) and Anything in analogy to substitution for DotTerm
        //@note Uniform substitution of the argument placeholder applied to the replacement subs.repl for the shape subs.what
        USubstRenChurch(toSubsPairs(wArg, theta)).usubst(repl.asInstanceOf[Term])
      case app@FuncOf(g:Function, theta) if !matchHead(app) => FuncOf(g, usubst(theta))
      case Nothing => Nothing
      case d: DotTerm        => subs.getOrElse(d, d).asInstanceOf[Term]
      case f: UnitFunctional => subs.getOrElse(f, f).asInstanceOf[Term]
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
    }
  } ensures(r => r.kind==term.kind && r.sort==term.sort, "Uniform Substitution leads to same kind and same sort " + term)

  /** uniform substitution on formulas */
  private def usubst(formula: Formula): Formula = {
    formula match {
      case p: UnitPredicational => subs.getOrElse(p, p).asInstanceOf[Formula]
      case app@PredOf(op, theta) if matchHead(app) =>
        val (what, repl) = matchHeads(op)
        val PredOf(wp, wArg) = what
        assert(wp == op, "match only if same head")
        assert(isDot(wArg) || wArg == Nothing)
        // unofficial substitution for Nothing (no effect) and Anything in analogy to substitution for DotTerm
        //@note Uniform substitution of the argument placeholder applied to the replacement subs.repl for the shape subs.what
        USubstRenChurch(toSubsPairs(wArg, theta)).usubst(repl.asInstanceOf[Formula])
      case app@PredOf(q, theta) if !matchHead(app) => PredOf(q, usubst(theta))
      case app@PredicationalOf(op, fml) if matchHead(app) =>
        requireAdmissible(allVars, fml, formula)
        val (what, repl) = matchHeads(op)
        val PredicationalOf(wp, wArg) = what
        assert(wp == op, "match only if same head")
        assert(wArg == DotFormula)
        USubstRenChurch((wArg, usubst(fml)) :: Nil).usubst(repl.asInstanceOf[Formula])
      case app@PredicationalOf(q, fml) if !matchHead(app) =>
        requireAdmissible(allVars, fml, formula)
        PredicationalOf(q, usubst(fml))
      case DotFormula => subs.getOrElse(DotFormula, DotFormula).asInstanceOf[Formula]
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
        Forall(vars.map(x => renameVar(x,formula)), usubst(g))
      case Exists(vars, g) => requireAdmissible(SetLattice(vars), g, formula)
        Exists(vars.map(x => renameVar(x,formula)), usubst(g))

      // Note could optimize speed by avoiding duplicate computation unless Scalac knows about CSE
      case Box(p, g) => requireAdmissible(StaticSemantics(usubst(p)).bv, g, formula)
        Box(usubst(p), usubst(g))
      case Diamond(p, g) => requireAdmissible(StaticSemantics(usubst(p)).bv, g, formula)
        Diamond(usubst(p), usubst(g))
    }
  } ensures(r => r.kind==formula.kind && r.sort==formula.sort, "Uniform Substitution leads to same kind and same sort " + formula)

  /** uniform substitution on programs */
  private def usubst(program: Program): Program = {
    program match {
      case a: ProgramConst   => subs.getOrElse(a, a).asInstanceOf[Program]
      case a: SystemConst    => subs.getOrElse(a, a).asInstanceOf[Program]
      case Assign(x, e)      => Assign(renameVar(x, program), usubst(e))
      case AssignAny(x)      => AssignAny(renameVar(x, program))
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
  } ensures(r => r.kind==program.kind && r.sort==program.sort, "Uniform Substitution leads to same kind and same sort " + program)

  /** uniform substitution on differential programs */
  private def usubst(ode: DifferentialProgram): DifferentialProgram = {
    //@note This case is a mixture of AtomicODE and ProgramConst. Only admissibility wrt BV still bound in the result (after substitution of DifferentialProgramConst) but admissible within the whole system simultaneously.
    //@note Conceptually easiest (albeit suboptimally efficient): pre-substitute without taboos to determine BV, then check admissibility during the proper substitution w.r.t. those BV as in other cases.
    requireAdmissible(StaticSemantics(usubstODE(ode, SetLattice.bottom)).bv, ode, ode)
    //@note the requires checking within usubstODE(ode, odeBV) will be redundant but locally the right thing to do.
    //@note usubstODE(ode, StaticSemantics(usubstODE(ode, SetLattice.bottom)).bv) would be sound just more permissive
    usubstODE(ode, StaticSemantics(ode).bv)
  } ensures(r => r.kind==ode.kind && r.sort==ode.sort, "Uniform Substitution leads to same kind and same sort " + ode)

  //@todo augment admissibility checks with vars before and after renaming. Enough to do in requireAdmissible?

  /**
   * uniform substitutions on differential programs
   * @param odeBV the bound variables of the whole ODESystem within which ode occurs, so all odeBV are taboo during the substitution.
   */
  private def usubstODE(ode: DifferentialProgram, odeBV: SetLattice[Variable]): DifferentialProgram = {
    ode match {
      case AtomicODE(DifferentialSymbol(x), e) => requireAdmissible(odeBV, e, ode)
        AtomicODE(DifferentialSymbol(renameVar(x, ode)), usubst(e))
      case c: DifferentialProgramConst => subs.getOrElse(c, c).asInstanceOf[DifferentialProgram]
      // homomorphic cases
      case DifferentialProduct(a, b) => DifferentialProduct(usubstODE(a, odeBV), usubstODE(b, odeBV))
    }
  } ensures(r => r.kind==ode.kind && r.sort==ode.sort, "Uniform Substitution leads to same kind and same sort " + ode)

  // admissibility
  
  /**
   * Is this uniform substitution U-admissible for expression e?
   */
  private def admissible(U: SetLattice[Variable], e: Expression): Boolean = admissible(U, StaticSemantics.signature(e))

  /**
   * Require that this uniform substitution is U-admissible for expression e, and
   * raise informative exception if not.
   */
  private def requireAdmissible(U: SetLattice[Variable], e: Expression, context: Expression): Unit =
    if (!admissible(U, e))
      throw new SubstitutionClashException(toString, U.prettyString, e.prettyString, context.prettyString, clashSet(U, e).prettyString, "")

  /**
   * check whether this substitution is U-admissible for an expression with the given occurrences of functions/predicates symbols.
   * @param U taboo list of variables
   * @param occurrences the function and predicate symbols occurring in the expression of interest.
   * @see arXiv:1503.01981 Definition 12.
   */
  private def admissible(U: SetLattice[Variable], occurrences: immutable.Set[NamedSymbol]): Boolean =
    // U-admissible iff FV(restrict this to occurrences) /\ U = empty
    clashSet(U, occurrences).isEmpty
    // this + " is " + U + "-admissible iff restriction " + projection(occurrences) + " to occurring symbols " + occurrences + " has no free variables " + projection(occurrences).freeVars + " of " + U)

  /**
   * Projects / restricts a substitution to only those that affect the symbols listed in occurrences.
   * @see arXiv:1503.01981 Definition 12.
   */
  private def projection(affected: immutable.Set[NamedSymbol]): USubstRenChurch = new USubstRenChurch(
    subsDefsInput.filter(sp => sp._1 match {
      case app: ApplicationOf => affected.contains(app.func)
      case _ => true
    })
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
  private def clashSet(U: SetLattice[Variable], e: Expression): SetLattice[Variable] = clashSet(U, StaticSemantics.signature(e))

  /**
   * Compute the set of all symbols for which this substitution clashes because it is not U-admissible
   * for an expression with the given occurrences of functions/predicates symbols.
   * @param U taboo list of variables
   * @param occurrences the function and predicate symbols occurring in the expression of interest.
   * @return FV(restrict this to occurrences) /\ U
   * @see arXiv:1503.01981 Definition 12.
   */
  private def clashSet(U: SetLattice[Variable], occurrences: immutable.Set[NamedSymbol]): SetLattice[Variable] =
    projection(occurrences).freeVars.intersect(U)

  /**
   * Get the unique element in c to which pred applies.
   * Protests if that element is not unique because pred applies to more than one element in c or if there is none.
   */
  private def uniqueElementOf[E](c: Iterable[E], pred: E => Boolean): E = {
    //require(c.count(pred) == 1, "unique element expected in " + c.mkString)
    val matching = c.filter(pred)
    require(matching.tail.isEmpty, "unique elemented expected in " + c.mkString)
    matching.head
  }

  /** Turns matching terms into substitution pairs (traverses pairs to create component-wise substitutions). */
  private def toSubsPairs(w: Term, r: Term): List[(Term, Term)] = (w, r) match {
    case (Pair(wl, wr), Pair(rl, rr)) => toSubsPairs(wl, rl) ++ toSubsPairs(wr, rr)
    case _ => w -> usubst(r) :: Nil
  }

  /** Indicates whether the term `t` is a DotTerm or nested pairs of DotTerms. */
  private def isDot(t: Term): Boolean = t match {
    case _: DotTerm => true
    case Pair(l, r) => isDot(l) && isDot(r)
    case _ => false
  }
}
