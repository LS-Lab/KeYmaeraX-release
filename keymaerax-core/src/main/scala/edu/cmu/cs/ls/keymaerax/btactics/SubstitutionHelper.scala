/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._

import scala.collection.immutable.Set

/**
 * Created by smitsch on 2/19/15.
 * @author Stefan Mitsch
 * @todo generalize to replacing formula by formula, too.
 */
object SubstitutionHelper {
  /** Return the result of replacing all free occurrences of `what` in formula `f` by `repl`. */
  def replaceFree(f: Formula)(what: Term, repl:Term): Formula =
    new SubstitutionHelper(what, repl).usubst(SetLattice.bottom[Variable], SetLattice.bottom[Variable], f)
  /** Return the result of replacing all free occurrences of `what` in formula `f` by `repl`. */
  def replaceFree(t: Term)(what: Term, repl:Term): Term =
    new SubstitutionHelper(what, repl).usubst(SetLattice.bottom[Variable], SetLattice.bottom[Variable], t)
  /** Return the result of replacing all free occurrences of `what` in sequent `seq` by `repl`. */
  def replaceFree(seq: Sequent)(what: Term, repl:Term): Sequent =
    new Sequent(seq.ante.map((f:Formula)=>replaceFree(f)(what,repl)), seq.succ.map((f:Formula)=>replaceFree(f)(what,repl)))
}

class SubstitutionHelper(what: Term, repl: Term) {

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
    t match {
      // homomorphic cases
      case Neg(e) if t != what => Neg(usubst(o, u, e))
      case Neg(e) if t == what && u.intersect(StaticSemantics(t)).isEmpty => repl
      case Plus(l, r) if t != what => Plus(usubst(o, u, l), usubst(o, u, r))
      case Plus(l, r) if t == what && u.intersect(StaticSemantics(t)).isEmpty => repl
      case Minus(l, r) if t != what => Minus(usubst(o, u, l), usubst(o, u, r))
      case Minus(l, r) if t == what && u.intersect(StaticSemantics(t)).isEmpty => repl
      case Times(l, r) if t != what => Times(usubst(o, u, l), usubst(o, u, r))
      case Times(l, r) if t == what && u.intersect(StaticSemantics(t)).isEmpty => repl
      case Divide(l, r) if t != what => Divide(usubst(o, u, l), usubst(o, u, r))
      case Divide(l, r) if t == what && u.intersect(StaticSemantics(t)).isEmpty => repl
      case Power(l, r) if t != what => Power(usubst(o, u, l), usubst(o, u, r))
      case Power(l, r) if t == what && u.intersect(StaticSemantics(t)).isEmpty => repl
      // base cases
      case x: Variable if !u.contains(x) && x == what => repl
      case x: Variable if  u.contains(x) || x != what => x
//      case d: DifferentialSymbol if d == what => repl
//      case d: DifferentialSymbol if d != what => d
      case d: Differential if d == what => repl
      case d: Differential if d != what => d
      case app@FuncOf(fn, theta) if /*!u.contains(fn) &&*/ app == what => repl
      case app@FuncOf(fn, theta) if  /*u.contains(fn) ||*/ app != what => FuncOf(fn, usubst(o, u, theta))
      case Nothing => Nothing
      case Number(_) if t == what => repl
      case x: AtomicTerm => x
      case Pair(l, r) if t != what => Pair(usubst(o, u, l), usubst(o, u, r))
      case Pair(l, r) if t == what && u.intersect(StaticSemantics(t)).isEmpty => repl
      case _ => throw new UnknownOperatorException("Not implemented yet", t)
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
    case _ => throw new UnknownOperatorException("Not implemented yet", f)
  }

  private def usubst(o: SetLattice[Variable], u: SetLattice[Variable], p: Program): USR = p match {
    case Assign(x, e) => USR(o+x, u+x, Assign(x, usubst(o, u, e)))
    //case DiffAssign(d@DifferentialSymbol(x), e) => USR(o+x, u+x, DiffAssign(d, usubst(o, u, e)))
    case AssignAny(x) => USR(o+x, u+x, p)
    case Test(f) => USR(o, u, Test(usubst(o, u, f)))
      //@todo double-check this case
    case ODESystem(ode, h) => val x = primedVariables(ode);
      val sode = usubst(o, u, x, ode);
      val ssys = ODESystem(sode, usubst(o++SetLattice(x), u++SetLattice(x), h))
      USR(o++SetLattice(x), u++SetLattice(x), ssys)
    case ode: DifferentialProgram => val x = primedVariables(ode); val sode = usubst(o, u, x, ode); USR(o++SetLattice(x), u++SetLattice(x), sode)
    case Compose(a, b) => val USR(q, v, as) = usubst(o, u, a); val USR(r, w, bs) = usubst(q, v, b); USR(r, w, Compose(as, bs))
    case Choice(a, b) =>
      val USR(q, v, as) = usubst(o, u, a); val USR(r, w, bs) = usubst(o, u, b)
      USR(q.intersect(r), v++w, Choice(as, bs))
    case Loop(a) => val USR(q, v, _) = usubst(o, u, a); val USR(r, w, as) = usubst(o, v, a); USR(o, w, Loop(as))
    case Dual(a) => val USR(q, v, as) = usubst(o, u, a); USR(q, v, Dual(as))
    case _ => throw new UnknownOperatorException("Not implemented yet", p)
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
    case AtomicODE(d@DifferentialSymbol(x), e) => AtomicODE(d, usubst(o++SetLattice(primed), u++SetLattice(primed), e))
    case _: DifferentialProgramConst => p
  }

  private def primedVariables(ode: DifferentialProgram): Set[Variable] = ode match {
    case DifferentialProduct(a, b) => primedVariables(a) ++ primedVariables(b)
    case AtomicODE(DifferentialSymbol(x), _) => Set(x)
    case _: DifferentialProgramConst => Set.empty
  }
}
