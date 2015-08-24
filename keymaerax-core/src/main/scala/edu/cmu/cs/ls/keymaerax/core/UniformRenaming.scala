/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
/**
 * Uniform Renaming for KeYmaera X
 * @author Andre Platzer
 * @see "Andre Platzer. A uniform substitution calculus for differential dynamic logic.  arXiv 1503.01981, 2015."
 * @note Code Review: 2015-08-24
 */
package edu.cmu.cs.ls.keymaerax.core

// require favoring immutable Seqs for soundness

import edu.cmu.cs.ls.keymaerax.core.StaticSemantics

import scala.collection.immutable

/**
 * Uniformly rename all occurrences of variable what (and its associated DifferentialSymbol) to repl everywhere.
 * @param what What variable to replace (along with its associated DifferentialSymbol).
 * @param repl The target variable to replace what with.
 * @requires only used when repl does not occur in the input.
 * @author smitsch
 * @author Andre Platzer
 */
final case class URename(what: Variable, repl: Variable) extends (Expression => Expression) {
  require(what.sort == repl.sort, "Uniform renaming only to variables of the same sort")
  /** The variables that are not allowed to occur initially */
  private val taboo: Set[NamedSymbol] = if (repl.sort == Real) Set(repl,DifferentialSymbol(repl)) else Set(repl)
  /** The variables that are affected and should be gone finally */
  private val affected: Set[NamedSymbol] = if (what.sort == Real) Set(what,DifferentialSymbol(what)) else Set(what)

  /** Whether to allow semantic renaming, i.e., renaming within ProgramConst etc that do not have a syntactic representation of what. */
  //@todo Code Review: This should be false to disallow renaming within semantic constructs. Change to false after adapting tactics.
  private val semanticRenaming: Boolean = System.getProperty("LAX", "true")=="true"

  override def toString: String = "URename{" + what + "~>" + repl + "}"


  /** apply this uniform renaming everywhere in an expression, resulting in an expression of the same kind. */
  def apply(e: Expression): Expression = e match {
    case t: Term => apply(t)
    case f: Formula => apply(f)
    case p: Program => apply(p)
  }

  /** apply this uniform renaming everywhere in a term */
  def apply(t: Term): Term = { try rename(t) catch { case ex: ProverException => throw ex.inContext(t.prettyString) }
  } ensuring(r => StaticSemantics.symbols(t).intersect(taboo).isEmpty, "Renamed only to new names that do not occur yet " + repl + " cannot occur in " + t
    ) ensuring(r => repl==what || StaticSemantics.symbols(r).intersect(affected).isEmpty, "Uniform Renaming replaced all occurrences (except when identity renaming)")

  /** apply this uniform renaming everywhere in a formula */
  def apply(f: Formula): Formula = { try rename(f) catch { case ex: ProverException => throw ex.inContext(f.prettyString) }
  } ensuring(r => StaticSemantics.symbols(f).intersect(taboo).isEmpty, "Renamed only to new names that do not occur yet " + repl + " cannot occur in " + f
    ) ensuring(r => repl==what || StaticSemantics.symbols(r).intersect(affected).isEmpty, "Uniform Renaming replaced all occurrences (except when identity renaming)")

  /** apply this uniform renaming everywhere in a program */
  def apply(p: Program): Program = { try rename(p) catch { case ex: ProverException => throw ex.inContext(p.prettyString) }
  } ensuring(r => StaticSemantics.symbols(p).intersect(taboo).isEmpty, "Renamed only to new names that do not occur yet " + repl + " cannot occur in " + p
    ) ensuring(r => repl==what || StaticSemantics.symbols(r).intersect(affected).isEmpty, "Uniform Renaming replaced all occurrences (except when identity renaming)")

  /**
   * Apply uniform renaming everywhere in the sequent.
   */
  //@note mapping apply instead of the equivalent rename makes sure the exceptions are augmented and the ensuring contracts checked.
  def apply(s: Sequent): Sequent = try { Sequent(s.pref, s.ante.map(apply), s.succ.map(apply))
    } catch { case ex: ProverException => throw ex.inContext(s.toString) }

  // implementation

  /** Rename a variable (that occurs in the given context for error reporting purposes) */
  private def renameVar(x: Variable, context: Expression): Variable = if (x==what) repl
  else if (x==repl) throw new BoundRenamingClashException("Replacement name " + repl + " already occurs originally", context.toString)
  else x


  private def rename(term: Term): Term = term match {
    case x: Variable                      => renameVar(x, term)
    case DifferentialSymbol(x)            => DifferentialSymbol(renameVar(x, term))
    case n: Number                        => n
    case FuncOf(f:Function, theta)        => FuncOf(f, rename(theta))
    case Anything | Nothing | DotTerm     => term
    // homomorphic cases
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
    case PredicationalOf(c, fml) => throw new BoundRenamingClashException("Cannot replace semantic dependencies syntactically: Predicational " + formula, toString)
    case DotFormula         => if (semanticRenaming) DotFormula else throw new BoundRenamingClashException("Cannot replace semantic dependencies syntactically: Predicational " + formula, toString)
    case True | False       => formula

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

    // binding cases add bound variables to u
    case Forall(vars, g) => Forall(vars.map(x => renameVar(x,formula)), rename(g))
    case Exists(vars, g) => Exists(vars.map(x => renameVar(x,formula)), rename(g))

    case Box(p, g)       => Box(rename(p), rename(g))
    case Diamond(p, g)   => Diamond(rename(p), rename(g))
  }

  private def rename(program: Program): Program = program match {
    case a: ProgramConst             => if (semanticRenaming) a else throw new BoundRenamingClashException("Cannot replace semantic dependencies syntactically: ProgramConstant " + a, toString)
    case Assign(x, e)                => Assign(renameVar(x,program), rename(e))
    case DiffAssign(DifferentialSymbol(x), e) => DiffAssign(DifferentialSymbol(renameVar(x,program)), rename(e))
    case AssignAny(x)                => AssignAny(renameVar(x,program))
    case Test(f)                     => Test(rename(f))
    case ODESystem(a, h)             => ODESystem(renameODE(a), rename(h))
    case Choice(a, b)                => Choice(rename(a), rename(b))
    case Compose(a, b)               => Compose(rename(a), rename(b))
    case Loop(a)                     => Loop(rename(a))
    case Dual(a)                     => Dual(rename(a))
  }

  private def renameODE(ode: DifferentialProgram): DifferentialProgram = ode match {
    case AtomicODE(DifferentialSymbol(x), e) => AtomicODE(DifferentialSymbol(renameVar(x,ode)), rename(e))
    case c: DifferentialProgramConst => if (semanticRenaming) c else throw new BoundRenamingClashException("Cannot replace semantic dependencies syntactically: DifferentialProgramConstant " + c, toString)      // homomorphic cases
    case DifferentialProduct(a, b)   => DifferentialProduct(renameODE(a), renameODE(b))
  }
}