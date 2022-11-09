/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.infrastruct

import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable.Set

/**
 * Created by smitsch on 2/19/15.
 * @author Stefan Mitsch
 * @todo generalize to replacing formula by formula, too.
 */
object SubstitutionHelper {
  /** Return the result of replacing all free occurrences of `what` in term `t` by `repl` whenever `replaces(what) = Some(repl)`. */
  def replacesFree(f: Formula)(replaces: Term => Option[Term]): Formula =
    new SubstitutionHelper(replaces).usubst(SetLattice.bottom[Variable], SetLattice.bottom[Variable], f)
  /** Return the result of replacing all free occurrences of `what` in formula `f` by `repl` whenever `replaces(what) = Some(repl)`. */
  def replacesFree(t: Term)(replaces: Term => Option[Term]): Term =
    new SubstitutionHelper(replaces).usubst(SetLattice.bottom[Variable], SetLattice.bottom[Variable], t)
  /** Return the result of replacing all free occurrences of `what` in sequent `seq` by `repl` whenever `replaces(what) = Some(repl)`. */
  def replacesFree(seq: Sequent)(replaces: Term => Option[Term]): Sequent =
    Sequent(seq.ante.map((f:Formula)=>replacesFree(f)(replaces)), seq.succ.map((f:Formula)=>replacesFree(f)(replaces)))
  /** Return the result of replacing all free occurrences of `what` in program `prg` by `repl` whenever `replaces(what) = Some(repl)`. */
  def replacesFree(prg: Program)(replaces: Term => Option[Term]): Program =
    new SubstitutionHelper(replaces).usubst(SetLattice.bottom[Variable], SetLattice.bottom[Variable], prg).p
  /** Return the result of replacing all free occurrences of `what` in expression `expr` by `repl` whenever `replaces(what) = Some(repl)`. */
  def replacesFree[T <: Expression](expr: T)(replaces: Term => Option[Term]): T = expr match {
    case f: Formula => replacesFree(f)(replaces).asInstanceOf[T]
    case t: Term => replacesFree(t)(replaces).asInstanceOf[T]
    case p: Program => replacesFree(p)(replaces).asInstanceOf[T]
  }

  private def replaceOne(what: Term, repl: Term)(t: Term) : Option[Term] = if (what == t) Some(repl) else None
  /** Return the result of replacing all free occurrences of `what` in term `t` by `repl`. */
  def replaceFree(f: Formula)(what: Term, repl:Term): Formula = replacesFree(f)(replaceOne(what, repl))
  /** Return the result of replacing all free occurrences of `what` in formula `f` by `repl`. */
  def replaceFree(t: Term)(what: Term, repl:Term): Term = replacesFree(t)(replaceOne(what, repl))
  /** Return the result of replacing all free occurrences of `what` in sequent `seq` by `repl`. */
  def replaceFree(seq: Sequent)(what: Term, repl:Term): Sequent = replacesFree(seq)(replaceOne(what, repl))
  /** Return the result of replacing all free occurrences of `what` in program `prg` by `repl`. */
  def replaceFree(prg: Program)(what: Term, repl:Term): Program = replacesFree(prg)(replaceOne(what, repl))
  /** Return the result of replacing all free occurrences of `what` in expression `expr` by `repl`. */
  def replaceFree[T <: Expression](expr: T)(what: Term, repl:Term): T = replacesFree[T](expr)(replaceOne(what, repl))

  /** Replaces any function application `fn`(...) in `fml` per `subst`. */
  def replaceFn(fn: Function, fml: Formula, subst: Map[Term, Variable]): Formula = {
    ExpressionTraversal.traverse(new ExpressionTraversal.ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, t: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = t match {
        case FuncOf(mf: Function, t: Term) if mf == fn => Right(subst(t))
        case _ => Left(None)
      }
    }, fml) match {
      case Some(g) => g
    }
  }
}

class SubstitutionHelper(replace: Term => Option[Term]) {

  /**
   * Records the result of uniform substitution in a program.
   * @param o The ignore set.
   * @param u The taboo set.
   * @param p The program.
   */
  private sealed case class USR(o: SetLattice[Variable],
                                u: SetLattice[Variable],
                                p: Program)

  /**
   * @param u the set of taboo symbols that would clash substitutions if they occurred since they have been bound outside.
   */
  private def usubst(o: SetLattice[Variable], u: SetLattice[Variable], t: Term): Term = {
    (t, replace(t)) match {
      // homomorphic cases
      case (Neg(e), None) => Neg(usubst(o, u, e))
      case (Neg(_), Some(repl)) if u.intersect(StaticSemantics(t)).isEmpty => repl
      case (Plus(l, r), None) => Plus(usubst(o, u, l), usubst(o, u, r))
      case (Plus(_, _), Some(repl)) if u.intersect(StaticSemantics(t)).isEmpty => repl
      case (Minus(l, r), None) => Minus(usubst(o, u, l), usubst(o, u, r))
      case (Minus(_, _), Some(repl)) if u.intersect(StaticSemantics(t)).isEmpty => repl
      case (Times(l, r), None) => Times(usubst(o, u, l), usubst(o, u, r))
      case (Times(_, _), Some(repl)) if u.intersect(StaticSemantics(t)).isEmpty => repl
      case (Divide(l, r), None) => Divide(usubst(o, u, l), usubst(o, u, r))
      case (Divide(_, _), Some(repl)) if u.intersect(StaticSemantics(t)).isEmpty => repl
      case (Power(l, r), None) => Power(usubst(o, u, l), usubst(o, u, r))
      case (Power(_, _), Some(repl)) if u.intersect(StaticSemantics(t)).isEmpty => repl
      // base cases
      case (x: Variable, Some(repl)) if !u.contains(x) => repl
      case (x: Variable, _) => x
//      case d: DifferentialSymbol if d == what => repl
//      case d: DifferentialSymbol if d != what => d
      case (_: Differential, Some(repl)) => repl
      case (d: Differential, None) => d
      case (FuncOf(_, _), Some(repl)) if u.intersect(StaticSemantics(t)).isEmpty =>
        requireAdmissible(u, StaticSemantics(repl), repl, t)
        repl
      case (FuncOf(fn, theta), None) => FuncOf(fn, usubst(o, u, theta))
      case (Nothing, _) => Nothing
      case (Number(_), Some(repl)) => repl
      case (_: DotTerm, Some(repl)) => repl
      case (x: AtomicTerm, _) => x
      case (Pair(l, r), None) => Pair(usubst(o, u, l), usubst(o, u, r))
      case (Pair(_, _), Some(repl)) if u.intersect(StaticSemantics(t)).isEmpty => repl
      case (_, Some(_)) if !u.intersect(StaticSemantics(t)).isEmpty => t
      case _ => throw UnknownOperatorException("Not implemented yet", t)
    }
  }

  private def usubst(o: SetLattice[Variable], u: SetLattice[Variable], f: Formula): Formula = f match {
    // homomorphic cases
    case Not(g) => Not(usubst(o, u, g))
    case And(l, r) => And(usubst(o, u, l), usubst(o, u, r))
    case Or(l, r) => Or(usubst(o, u, l), usubst(o, u, r))
    case Imply(l, r) => Imply(usubst(o, u, l), usubst(o, u, r))
    case Equiv(l, r) => Equiv(usubst(o, u, l), usubst(o, u, r))

    case Equal(l, r) => Equal(usubst(o, u, l), usubst(o, u, r))
    case NotEqual(l, r) => NotEqual(usubst(o, u, l), usubst(o, u, r))
    case GreaterEqual(l, r) => GreaterEqual(usubst(o, u, l), usubst(o, u, r))
    case Greater(l, r) => Greater(usubst(o, u, l), usubst(o, u, r))
    case LessEqual(l, r) => LessEqual(usubst(o, u, l), usubst(o, u, r))
    case Less(l, r) => Less(usubst(o, u, l), usubst(o, u, r))

    // binding cases add bound variables to u
    case Forall(vars, g) => Forall(vars, usubst(o ++ vars, u ++ vars, g))
    case Exists(vars, g) => Exists(vars, usubst(o ++ vars, u ++ vars, g))

    case Box(p, g) => val USR(q, v, sp) = usubst(o, u, p); Box(sp, usubst(q, v, g))
    case Diamond(p, g) => val USR(q, v, sp) = usubst(o, u, p); Diamond(sp, usubst(q, v, g))

    // uniform substitution base cases
    case PredOf(fn, theta) => PredOf(fn, usubst(o, u, theta))
    case DifferentialFormula(g) => DifferentialFormula(usubst(o, u, g))
    case x: AtomicFormula => x
    case _ => throw UnknownOperatorException("Not implemented yet", f)
  }

  private def usubst(o: SetLattice[Variable], u: SetLattice[Variable], p: Program): USR = p match {
    case Assign(x, e) => USR(o+x, u+x, Assign(x, usubst(o, u, e)))
    //case DiffAssign(d@DifferentialSymbol(x), e) => USR(o+x, u+x, DiffAssign(d, usubst(o, u, e)))
    case AssignAny(x) => USR(o+x, u+x, p)
    case Test(f) => USR(o, u, Test(usubst(o, u, f)))
      //@todo double-check this case
    case ODESystem(ode, h) => val x = primedVariables(ode)
      val sode = usubst(o, u, x, ode)
      val ssys = ODESystem(sode, usubst(o++SetLattice(x), u++SetLattice(x), h))
      USR(o++SetLattice(x), u++SetLattice(x), ssys)
    case ode: DifferentialProgram => val x = primedVariables(ode); val sode = usubst(o, u, x, ode); USR(o++SetLattice(x), u++SetLattice(x), sode)
    case Compose(a, b) =>
      val USR(q, v, as) = usubst(o, u, a)
      val USR(r, w, bs) = usubst(q, v, b)
      USR(r, w, Compose(as, bs))
    case Choice(a, b) =>
      val USR(q, v, as) = usubst(o, u, a)
      val USR(r, w, bs) = usubst(o, u, b)
      USR(q.intersect(r), v++w, Choice(as, bs))
    case Loop(a) => val USR(_, v, _) = usubst(o, u, a); val USR(_, w, as) = usubst(o, v, a); USR(o, w, Loop(as))
    case Dual(a) => val USR(q, v, as) = usubst(o, u, a); USR(q, v, Dual(as))
    case a: ProgramConst => USR(o, SetLattice.allVars, a)
    case a: SystemConst => USR(o, SetLattice.allVars, a)
    case _ => throw UnknownOperatorException("Not implemented yet", p)
  }

  /**
   * Substitution in (systems of) differential equations.
   * @param o The ignore list.
   * @param u The taboo list.
   * @param primed The primed names (all primed names in the ODE system).
   * @param p The ODE.
   * @return The substitution result.
   */
  private def usubst(o: SetLattice[Variable], u: SetLattice[Variable], primed: Set[Variable], p: DifferentialProgram):
      DifferentialProgram = p match {
    case DifferentialProduct(a, b) => DifferentialProduct(usubst(o, u, primed, a), usubst(o, u, primed, b))
    case AtomicODE(d: DifferentialSymbol, e) => AtomicODE(d, usubst(o++SetLattice(primed), u++SetLattice(primed), e))
    case _: DifferentialProgramConst => p
  }

  private def primedVariables(ode: DifferentialProgram): Set[Variable] = ode match {
    case DifferentialProduct(a, b) => primedVariables(a) ++ primedVariables(b)
    case AtomicODE(DifferentialSymbol(x), _) => Set(x)
    case _: DifferentialProgramConst => Set.empty
  }

  @inline private def requireAdmissible(taboo: SetLattice[Variable], frees: SetLattice[Variable], e: Expression, context: Expression): Unit = {
    val clashes = taboo.intersect(frees)
    if (!clashes.isEmpty)
      throw SubstitutionClashException(toString, taboo.prettyString, e.prettyString, context.prettyString, clashes.prettyString, "")
  }
}
