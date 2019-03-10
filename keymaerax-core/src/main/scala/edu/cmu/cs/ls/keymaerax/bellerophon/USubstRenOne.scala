/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.core.SetLattice._
import edu.cmu.cs.ls.keymaerax.core._
import SetLattice.allVars
import SetLattice.bottom
import edu.cmu.cs.ls.keymaerax.core.StaticSemantics.{apply => _, _}

import scala.collection.immutable
import scala.collection.immutable._

object USubstRenOne {
  @inline
  private val optima = true
}

/** Like a SubstitutionPair but not checked.
  *
  * @param what
  * @param repl
  */
final case class URenSubstitutionPair(what: Expression, repl: Expression) {
  /**
    * The (new) free variables that this substitution introduces (without DotTerm/DotFormula arguments).
    * That is the (new) free variables introduced by this substitution, i.e. free variables of repl that are not bound as arguments in what.
    * @return essentially freeVars(repl) except for special handling of UnitFunctional and UnitPredicational arguments.
    * @see Definition 19 in Andre Platzer. [[https://doi.org/10.1007/s10817-016-9385-1 A complete uniform substitution calculus for differential dynamic logic]]. Journal of Automated Reasoning, 2016.
    * @see [[SubstitutionPair.freeVars]]
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
           ProgramConst(_, _) | SystemConst(_) | DifferentialProgramConst(_, _) => bottom
    }
    case _ => StaticSemantics.freeVars(repl)
  }

  /**
    * Check whether we match on the term other, i.e. both have the same head so the occurrence in other
    * should be replaced according to this SubstitutionPair.
    */
  def sameHead(other: ApplicationOf): Boolean = what match {
    case FuncOf(lf, arg) =>
      assert(SubstitutionAdmissibility.isSubstitutableArg(arg), "Only DotTerm/Nothing allowed as argument")
      other match { case FuncOf(rf, _) => lf == rf case _ => false }
    case PredOf(lf, arg) =>
      assert(SubstitutionAdmissibility.isSubstitutableArg(arg), "Only DotTerm/Nothing allowed as argument")
      other match { case PredOf(rf, _) => lf == rf case _ => false }
    case PredicationalOf(lf, arg) =>
      assert(arg match { case DotFormula => true case _ => false }, "Only DotFormula allowed as argument")
      other match { case PredicationalOf(rf, _) => lf == rf case _ => false }
    case _ => assert(false, "sameHead only used for ApplicationOf"); false
  }

}

/**
  * Standalone Renaming Uniform Substitution operation, simultaneously combining [[URename]] and [[USubst]]
  * to uniformly substitute while simultaneously uniformly renaming multiple variables.
  * This implementation uses one-pass uniform substitution implementation a la [[USubstOne]].
  * Liberal list of SubstitutionPair represented as merely a list of Pair,
  * where the Variable~>Variable replacements are by uniform renaming,
  * and the other replacements are by uniform substitution, simultaneously.
  *
  * @note This implementation performs semantic renaming.
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.core.URename]]
  * @see [[edu.cmu.cs.ls.keymaerax.core.USubstOne]]
  * @see [[MultiRename]]
  * @see [[USubstRenChurch]]
  */
//@todo admissibility needs to be augmented with renamed variables too for soundness.
//@todo does not check soundness-critical occurrence constraints for Taboos, but the core ultimately will.
final case class USubstRenOne(private[bellerophon] val subsDefsInput: immutable.Seq[(Expression,Expression)]) extends (Expression => Expression) {
  import USubstRenOne.optima
  insist(subsDefsInput.forall(sp => sp._1.kind == sp._2.kind), "Substitution renaming only to expressions of the same kind: " + this)
  insist(subsDefsInput.forall(sp => sp._1.sort == sp._2.sort), "Substitution renaming only to expressions of the same sort: " + this)
  insist({val repls = subsDefsInput.map(sp=>sp._1).toList; repls.length == repls.distinct.length}, "No contradictory or duplicate substitutions/renamings: " + this)

  /** substitution part */
  private val subsDefs: immutable.Map[Expression,URenSubstitutionPair] = subsDefsInput.filter(sp => !sp._1.isInstanceOf[Variable]).map(
    sp => (sp._1,URenSubstitutionPair(sp._1,sp._2))
  ).toMap
  /** renaming part, augmented with transpositions */
  private val rens: immutable.Map[Variable,Variable] = augmentTranspositions(RenUSubst.renamingPartOnly(subsDefsInput).toMap)

  /** include transpositions for renamings if need be */
  private def augmentTranspositions(rena: immutable.Map[Variable,Variable]): immutable.Map[Variable,Variable] = {
    insist(rena.keySet.intersect(rena.values.toSet).isEmpty, "No replacement of a variable should be renamed in cyclic ways again: " + this)
    if (USubstRenChurch.TRANSPOSITION)
      rena ++ (rena.map(sp => sp._2->sp._1))
    else
      rena
  } ensuring( r => !USubstRenChurch.TRANSPOSITION || rena.forall(sp => r.get(sp._1)==Some(sp._2) && r.get(sp._2)==Some(sp._1)), "converse renamings are contained for " + rena)

  /** the ApplicationOf subset of subs with matching heads */
  private val matchHeads: immutable.Map[Function,(ApplicationOf,Expression)] =
    subsDefsInput.filter(sp => sp._1.isInstanceOf[ApplicationOf]).map(
      sp => {
        val app = sp._1.asInstanceOf[ApplicationOf]
        (app.func, (app, sp._2))
      }).toMap

  //if (BelleExpr.DEBUG) println("DOING " + this + "  with  rens=" + rens.map(sp => sp._1.prettyString + "~~>" + sp._2.prettyString).mkString(",") + "  subs=" + subs.map(sp => sp._1.prettyString + "~>" + sp._2.prettyString).mkString(",") + "  heads=" + matchHeads)

  //@todo check for substitutable expressions like in USubst

  override def toString: String = "USubstRen{" + subsDefsInput.map(sp => sp._1.prettyString + "~>" + sp._2.prettyString).mkString(", ") + "}"


  /** This USubstRen implemented strictly from the core.
    * Implemented by performing successive uniform renamings composed with renaming-aware uniform substitution. */
  val toCore: Expression => Expression = e => {
    val renall = MultiRename(RenUSubst.renamingPartOnly(subsDefsInput))
    // rename all substitutions (by transposition) since they'll be renamed back subsequently
    val usubst = USubstOne(subsDefs.toList.map(sp => SubstitutionPair(sp._1, renall(sp._2.repl))))
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
  }

  /** apply this uniform substitution renaming everywhere in a term */
  def apply(t: Term): Term = try usubst(bottom, t) catch { case ex: ProverException => throw ex.inContext(t.prettyString) }

  /** apply this uniform substitution renaming everywhere in a formula */
  def apply(f: Formula): Formula = try usubst(bottom, f) catch { case ex: ProverException => throw ex.inContext(f.prettyString) }

  /** apply this uniform substitution renaming everywhere in a differential program */
  def apply(p: DifferentialProgram): DifferentialProgram = try usubstODE(boundVars(p), p).asInstanceOf[DifferentialProgram] catch {case ex: ProverException => throw ex.inContext(p.prettyString)}

  /** apply this uniform substitution renaming everywhere in a program */
  def apply(p: Program): Program = try usubst(bottom[Variable], p)._2 catch { case ex: ProverException => throw ex.inContext(p.prettyString) }

  /**
   * Apply uniform substitution renaming everywhere in the sequent.
   */
  //@note mapping apply instead of the equivalent rename makes sure the exceptions are augmented and the ensuring contracts checked.
  def apply(s: Sequent): Sequent = try { Sequent(s.ante.map(apply), s.succ.map(apply))
  } catch { case ex: ProverException => throw ex.inContext(s.toString) }


  // implementation

  /**
    * Whether this substitution matches to replace the given expression e,
    * because there is a substitution pair that matches e.
    */
  private def matchHead(e: ApplicationOf): Boolean = matchHeads.contains(e.func)

  /** Rename a variable */
  private def renameVar(x: Variable): Variable = rens.get(x) match {
    case Some(repl) => repl
    case None => x match {
      case DifferentialSymbol(y) => DifferentialSymbol(renameVar(y))
      case _ => x
    }
  }

  // implementation of uniform substitution application
      
  /** uniform substitution on terms */
  private def usubst(u: SetLattice[Variable], term: Term): Term = {
    term match {
      // uniform substitution base cases
      case x: Variable => renameVar(x)
//      case DifferentialSymbol(x) => DifferentialSymbol(renameVar(x, term))
      case app@FuncOf(of, theta) if matchHead(app) =>
        val subs = uniqueElementOf[Expression,URenSubstitutionPair](subsDefs, (e,sp) => sp.what.isInstanceOf[FuncOf] && sp.sameHead(app))
        val FuncOf(wf, wArg) = subs.what
        assert(wf == of, "match on same function heads")
        assert(SubstitutionAdmissibility.isSubstitutableArg(wArg))
        requireAdmissible(u, subs.freeVars, subs.repl, term)
        // unofficial substitution for Nothing (no effect) and Anything in analogy to substitution for DotTerm
        //@note Uniform substitution of the argument placeholder applied to the replacement subs.repl for the shape subs.what
        USubstRenOne(toSubsPairs(u, wArg, theta)).usubst(bottom[Variable], subs.repl.asInstanceOf[Term])
      case app@FuncOf(g:Function, theta) if !matchHead(app) => FuncOf(g, usubst(u, theta))
      case Nothing => Nothing
      case d: DotTerm => subsDefs.getOrElse(d, URenSubstitutionPair(d,d)).repl.asInstanceOf[Term]
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
      case f: UnitFunctional => subsDefs.getOrElse(f, URenSubstitutionPair(f,f)).repl.asInstanceOf[Term]
    }
  }

  /** uniform substitution on formulas */
  private def usubst(u: SetLattice[Variable], formula: Formula): Formula = {
    formula match {
      case app@PredOf(op, theta) if matchHead(app) =>
        val subs = uniqueElementOf[Expression,URenSubstitutionPair](subsDefs, (e,sp) => sp.what.isInstanceOf[PredOf] && sp.sameHead(app))
        val PredOf(wp, wArg) = subs.what
        assert(wp == op, "match only if same head")
        assert(SubstitutionAdmissibility.isSubstitutableArg(wArg))
        requireAdmissible(u, subs.freeVars, subs.repl, formula)
        // unofficial substitution for Nothing (no effect) and Anything in analogy to substitution for DotTerm
        //@note Uniform substitution of the argument placeholder applied to the replacement subs.repl for the shape subs.what
        USubstRenOne(toSubsPairs(u, wArg, theta)).usubst(bottom[Variable], subs.repl.asInstanceOf[Formula])
      case app@PredOf(q, theta) if !matchHead(app) => PredOf(q, usubst(u, theta))
      // unofficial
      case app@PredicationalOf(op, fml) if matchHead(app) =>
        val subs = uniqueElementOf[Expression,URenSubstitutionPair](subsDefs, (e,sp) => sp.what.isInstanceOf[PredicationalOf] && sp.sameHead(app))
        val PredicationalOf(wp, wArg) = subs.what
        assert(wp == op, "match only if same head")
        assert(wArg == DotFormula)
        USubstRenOne(wArg -> usubst(allVars, fml) :: Nil).usubst(bottom[Variable], subs.repl.asInstanceOf[Formula])
      // unofficial
      case app@PredicationalOf(q, fml) if !matchHead(app) =>
        //@note admissibility is required for nonmatching predicationals since the arguments might be evaluated in different states.
        PredicationalOf(q, usubst(allVars, fml))
      case DotFormula => subsDefs.getOrElse(DotFormula, URenSubstitutionPair(DotFormula,DotFormula)).repl.asInstanceOf[Formula]
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
      case Forall(vars, g) => val renv=vars.map(x => renameVar(x)); Forall(renv, usubst(u++renv, g))
      case Exists(vars, g) => val renv=vars.map(x => renameVar(x)); Exists(renv, usubst(u++renv, g))

      case Box(p, g)     => val (v,rp) = usubst(u,p); Box(rp, usubst(v,g))
      case Diamond(p, g) => val (v,rp) = usubst(u,p); Diamond(rp, usubst(v,g))
      case p: UnitPredicational => subsDefs.getOrElse(p, URenSubstitutionPair(p,p)).repl.asInstanceOf[Formula]
    }
  }

  /** uniform substitution on programs */
  private def usubst(u: SetLattice[Variable], program: Program): (SetLattice[Variable],Program)  = {
    program match {
      case a: ProgramConst =>
        val r = subsDefs.getOrElse(a, URenSubstitutionPair(a,a)).repl.asInstanceOf[Program]
        (u++boundVars(r), r)
      //@todo optimizable: store boundVars(ProgramConst/SystemConst/DifferentialProgramConst) in substitution pair
      //@todo improve: for ProgramConst(_,Taboo(except)) could return allVars-except
      case a: SystemConst=>
        val r = subsDefs.getOrElse(a, URenSubstitutionPair(a,a)).repl.asInstanceOf[Program]
        (u++boundVars(r), r)
      case Assign(x, e)      => val rx=renameVar(x); (u+rx, Assign(rx, usubst(u,e)))
      case AssignAny(x)      => val rx=renameVar(x); (u+rx, AssignAny(rx))
      case Test(f)           => (u, Test(usubst(u,f)))
      case ODESystem(ode, h) =>
        //@todo improve: could make smaller for substituted DifferentialProgramConst
        //@todo rename boundVars
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
  //@todo augment admissibility checks with vars before and after renaming. Enough to do in requireAdmissible?
  private def usubstODE(v: SetLattice[Variable], ode: DifferentialProgram): DifferentialProgram = {
    ode match {
      case AtomicODE(DifferentialSymbol(x), e) =>
        //assert(v.contains(DifferentialSymbol(x)) && v.contains(x), "all bound variables already added to ODE taboos")
        AtomicODE(DifferentialSymbol(renameVar(x)), usubst(v, e))
      //@note Space compliance already checked in SubstitutionPair construction.
      case c: DifferentialProgramConst => subsDefs.getOrElse(c, URenSubstitutionPair(c,c)).repl.asInstanceOf[DifferentialProgram]
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
  private def toSubsPairs(taboo: SetLattice[Variable], w: Term, r: Term): Seq[(Term,Term)] = (w, r) match {
    case (Pair(wl, wr), Pair(rl, rr)) => toSubsPairs(taboo, wl, rl) ++ toSubsPairs(taboo, wr, rr)
    case _ => w->usubst(taboo, r) :: Nil
  }

  /**
    * Get the unique element in c to which pred applies.
    * Protests if that element is not unique because pred applies to more than one element in c or if there is none.
    */
  @inline private def uniqueElementOf[E,V](c: Map[E,V], pred: (E,V) => Boolean): V = {
    //require(c.count(pred) == 1, "unique element expected in " + c.mkString)
    val matching = c.filter(sp=>pred(sp._1,sp._2))
    require(matching.tail.isEmpty, "unique elemented expected in " + c.mkString)
    matching.head._2
  }

  // optimization

  /** Predict bound variables of this(program), whether substitution clashes or not.
    * @note Not soundness-critical as result checked by inclusion for other usubst round */
  private def substBoundVars(program: Program): SetLattice[Variable] = {
    program match {
      // base cases
      //@todo optimizable: store boundVars(ProgramConst/SystemConst/DifferentialProgramConst) in substitution pair
      case a: ProgramConst if subsDefs.contains(a) =>
        StaticSemantics.boundVars(subsDefs.get(a).get.repl.asInstanceOf[Program])
      case a: ProgramConst if !subsDefs.contains(a) => StaticSemantics.spaceVars(a.space)
      case a: SystemConst  if subsDefs.contains(a) =>
        StaticSemantics.boundVars(subsDefs.get(a).get.repl.asInstanceOf[Program])
      case a: SystemConst  if !subsDefs.contains(a) => allVars
      case c: DifferentialProgramConst if subsDefs.contains(c) =>
        StaticSemantics.boundVars(subsDefs.get(c).get.repl.asInstanceOf[DifferentialProgram])
      case c: DifferentialProgramConst if !subsDefs.contains(c) => StaticSemantics.spaceVars(c.space)
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