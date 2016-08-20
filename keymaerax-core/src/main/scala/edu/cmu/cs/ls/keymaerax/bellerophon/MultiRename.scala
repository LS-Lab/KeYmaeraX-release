/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.bellerophon

import edu.cmu.cs.ls.keymaerax.btactics.{Idioms, ProofRuleTactics}
import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable
import scala.collection.immutable._

/**
  * Uniformly rename multiple variables at once.
  * Uniformly all occurrences of `what` and `what'` to `repl` and `repl'` and vice versa,
  * for all (what,repl) in renames.
  *
  * Performs semantic renaming, i.e. leaves program constants etc. unmodified.
  * @author Andre Platzer
  * @see [[edu.cmu.cs.ls.keymaerax.core.URename]]
  */
final case class MultiRename(rens: immutable.Seq[(Variable,Variable)]) extends (Expression => Expression) {
  insist(rens.forall(sp => sp._1.sort == sp._2.sort), "Uniform renaming only to variables of the same sort: " + this)
  insist({val repls = rens.map(sp=>sp._1).toList; repls.length == repls.distinct.length}, "No contradictory or duplicate renamings: " + this)
  /** filtered without identity renaming */
  private val rena: immutable.Map[Variable,Variable] = rens.filter(sp => sp._1!=sp._2).toMap
  insist(rena.keySet.intersect(rena.values.toSet).isEmpty, "No replacement of a variable should be renamed yet again: " + this)
  /** including transpositions */
  private val renaming: immutable.Map[Variable,Variable] = {
    if (USubstRen.TRANSPOSITION)
      rena ++ (rena.map(sp => (sp._2,sp._1)))
    else
      rena
  } ensuring( r => !USubstRen.TRANSPOSITION || rena.forall(sp => r.get(sp._1)==Some(sp._2) && r.get(sp._2)==Some(sp._1)), "converse renamings are contained")

  /** `true` to also support program constants, predicationals etc and leaving them unmodified. 'false' to clash instead. */
  private val semanticRenaming: Boolean = true

  override def toString: String = "MultiRename{" + rens.map(sp => sp._1.toString + "~>" + sp._2).mkString(", ") + "}"

  /** This MultiRename implemented strictly from the core (but limited to no semantic renaming). */
  val toCore: Expression => Expression =
  //@note core renaming only uses without transposition augmentation
    e => rena.foldLeft(e)((expr,sp)=>URename(sp._1,sp._2)(expr))


  /** apply this uniform renaming everywhere in an expression, resulting in an expression of the same kind. */
  def apply(e: Expression): Expression = e match {
    case t: Term => apply(t)
    case f: Formula => apply(f)
    case p: DifferentialProgram => apply(p)
    case p: Program => apply(p)
  }

  /** apply this uniform renaming everywhere in a term */
  def apply(t: Term): Term = { try rename(t) catch { case ex: ProverException => throw ex.inContext(t.prettyString) }
  } ensuring (r => sameAsCore(t, r), "fast tactical renaming has same result as slower core renaming, if defined: " + this + " on " + t)

  /** apply this uniform renaming everywhere in a formula */
  def apply(f: Formula): Formula = { try rename(f) catch { case ex: ProverException => throw ex.inContext(f.prettyString) }
  } ensuring (r => sameAsCore(f, r), "fast tactical renaming has same result as slower core renaming, if defined: " + this + " on " + f)

  /** apply this uniform renaming everywhere in a program */
  def apply(p: DifferentialProgram): DifferentialProgram = { try renameODE(p) catch { case ex: ProverException => throw ex.inContext(p.prettyString) }
  } ensuring (r => sameAsCore(p, r), "fast tactical renaming has same result as slower core renaming, if defined: " + this + " on " + p)

  /** apply this uniform renaming everywhere in a program */
  def apply(p: Program): Program = { try rename(p) catch { case ex: ProverException => throw ex.inContext(p.prettyString) }
} ensuring (r => sameAsCore(p, r), "fast tactical renaming has same result as slower core renaming, if defined: " + this + " on " + p)

  /**
   * Apply uniform renaming everywhere in the sequent.
   */
  //@note mapping apply instead of the equivalent rename makes sure the exceptions are augmented and the ensuring contracts checked.
  def apply(s: Sequent): Sequent = try { Sequent(s.ante.map(apply), s.succ.map(apply))
  } catch { case ex: ProverException => throw ex.inContext(s.toString) }

  /** Check that same result as from core if both defined */
  private def sameAsCore(e: Expression, r: Expression): Boolean = {
    if (BelleExpr.RECHECK) try {
      if (r == toCore(e))
        true
      else {
        Predef.print("fast result: " + r + "\ncore result: " + toCore(e) + "\nmultiren:   " + this + "\nrenaming:   " + renaming + "\napplied to:  " + e)
        false
      }
    } catch {
      // the core refuses semantic renaming so cannot compare
      case ignore: RenamingClashException => true
    }
    else true
  }

  // implementation

  /** Rename a variable (that occurs in the given context for error reporting purposes) */
  private def renameVar(x: Variable, context: Expression): Variable = renaming.get(x) match {
    case Some(repl) => repl
    case None => x match {
      case DifferentialSymbol(y) => DifferentialSymbol(renameVar(y, context))
      case _ => x
    }
  }


  private def rename(term: Term): Term = term match {
    case x: Variable                      => renameVar(x, term)
    case n: Number                        => n
    case FuncOf(f:Function, theta)        => FuncOf(f, rename(theta))
    case Nothing | DotTerm(_)             => term
    case UnitFunctional(f,Except(v),sort) => if (semanticRenaming) UnitFunctional(f,Except(renameVar(v,term)),sort) else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: UnitFunctional " + term, this.toString, term.toString)
    case _: UnitFunctional                => if (semanticRenaming) term else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: UnitFunctional " + term, this.toString, term.toString)
    // homomorphic cases
    //@note the following cases are equivalent to f.reapply but are left explicit to enforce revisiting this case when data structure changes.
    // case f:BinaryCompositeTerm => f.reapply(rename(f.left), rename(f.right))
    case Neg(e)       => Neg(rename(e))
    case Plus(l, r)   => Plus(rename(l),   rename(r))
    case Minus(l, r)  => Minus(rename(l),  rename(r))
    case Times(l, r)  => Times(rename(l),  rename(r))
    case Divide(l, r) => Divide(rename(l), rename(r))
    case Power(l, r)  => Power(rename(l),  rename(r))
    case Differential(e) =>  Differential(rename(e))
    // unofficial
    case Pair(l, r)   => Pair(rename(l),   rename(r))
  }

  private def rename(formula: Formula): Formula = formula match {
    case PredOf(p, theta)   => PredOf(p, rename(theta))
    case PredicationalOf(c, fml) => if (semanticRenaming) formula else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: Predicational " + formula, this.toString, formula.toString)
    case DotFormula         => if (semanticRenaming) formula else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: Predicational " + formula, this.toString, formula.toString)
    case UnitPredicational(p,Except(v)) => if (semanticRenaming) UnitPredicational(p,Except(renameVar(v,formula))) else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: Predicational " + formula, this.toString, formula.toString)
    case _: UnitPredicational => if (semanticRenaming) formula else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: Predicational " + formula, this.toString, formula.toString)
    case True | False       => formula

    //@note the following cases are equivalent to f.reapply but are left explicit to enforce revisiting this case when data structure changes.
    // case f:BinaryCompositeFormula => f.reapply(rename(f.left), rename(f.right))

    // pseudo-homomorphic base cases
    case Equal(l, r)        => Equal(rename(l),        rename(r))
    case NotEqual(l, r)     => NotEqual(rename(l),     rename(r))
    case GreaterEqual(l, r) => GreaterEqual(rename(l), rename(r))
    case Greater(l, r)      => Greater(rename(l),      rename(r))
    case LessEqual(l, r)    => LessEqual(rename(l),    rename(r))
    case Less(l, r)         => Less(rename(l),         rename(r))

    // homomorphic cases
    case Not(g)      => Not(rename(g))
    case And(l, r)   => And(rename(l),   rename(r))
    case Or(l, r)    => Or(rename(l),    rename(r))
    case Imply(l, r) => Imply(rename(l), rename(r))
    case Equiv(l, r) => Equiv(rename(l), rename(r))

    // NOTE DifferentialFormula in analogy to Differential
    case DifferentialFormula(g) => DifferentialFormula(rename(g))

    case Forall(vars, g) => Forall(vars.map(x => renameVar(x,formula)), rename(g))
    case Exists(vars, g) => Exists(vars.map(x => renameVar(x,formula)), rename(g))

    case Box(p, g)       => Box(rename(p), rename(g))
    case Diamond(p, g)   => Diamond(rename(p), rename(g))
  }

  private def rename(program: Program): Program = program match {
    case a: ProgramConst             => if (semanticRenaming) program else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: ProgramConstant " + a, this.toString, program.toString)
    case Assign(x, e)                => Assign(renameVar(x,program), rename(e))
    case AssignAny(x)                => AssignAny(renameVar(x,program))
    case Test(f)                     => Test(rename(f))
    case ODESystem(a, h)             => ODESystem(renameODE(a), rename(h))
    //@note This case happens for standalone uniform substitutions on differential programs such as x'=f() or c as they come up in unification for example.
    case ode: DifferentialProgram    => renameODE(ode)
    //@note the following cases are equivalent to f.reapply but are left explicit to enforce revisiting this case when data structure changes.
    // case f:BinaryCompositeProgram => f.reapply(rename(f.left), rename(f.right))
    case Choice(a, b)                => Choice(rename(a), rename(b))
    case Compose(a, b)               => Compose(rename(a), rename(b))
    case Loop(a)                     => Loop(rename(a))
    case Dual(a)                     => Dual(rename(a))
  }

  private def renameODE(ode: DifferentialProgram): DifferentialProgram = ode match {
    case AtomicODE(DifferentialSymbol(x), e) => AtomicODE(DifferentialSymbol(renameVar(x,ode)), rename(e))
    case DifferentialProgramConst(c,Except(v)) => if (semanticRenaming) DifferentialProgramConst(c,Except(renameVar(v,ode))) else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: DifferentialProgramConstant " + c, this.toString, ode.toString)
    case c: DifferentialProgramConst => if (semanticRenaming) ode else throw new RenamingClashException("Cannot replace semantic dependencies syntactically: DifferentialProgramConstant " + c, this.toString, ode.toString)
    // homomorphic cases
    case DifferentialProduct(a, b)   => DifferentialProduct(renameODE(a), renameODE(b))
  }
}
