package edu.cmu.cs.ls.keymaera.tactics

import edu.cmu.cs.ls.keymaera.core._

import scala.collection.immutable.Set

/**
 * Created by smitsch on 2/19/15.
 * @author Stefan Mitsch
 */
object SubstitutionHelper {
  def replaceFree(f: Formula)(what: Term, repl:Term) =
    new SubstitutionHelper(what, repl).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], f)
  def replaceFree(t: Term)(what: Term, repl:Term) =
    new SubstitutionHelper(what, repl).usubst(SetLattice.bottom[NamedSymbol], SetLattice.bottom[NamedSymbol], t)
}
class SubstitutionHelper(what: Term, repl: Term) {
  import BindingAssessment._

  /**
   * Records the result of uniform substitution in a program.
   * @param o The ignore set.
   * @param u The taboo set.
   * @param p The program.
   */
  private sealed case class USR(o: SetLattice[NamedSymbol],
                                u: SetLattice[NamedSymbol],
                                p: Program)

  /**
   * @param u the set of taboo symbols that would clash substitutions if they occurred since they have been bound outside.
   */
  private def usubst(o: SetLattice[NamedSymbol], u: SetLattice[NamedSymbol], t: Term): Term = {
    t match {
      // homomorphic cases
      case Neg(s, e) if t != what => Neg(s, usubst(o, u, e))
      case Neg(s, e) if t == what && u.intersect(BindingAssessment.freeVariables(t)).isEmpty => repl
      case Add(s, l, r) if t != what => Add(s, usubst(o, u, l), usubst(o, u, r))
      case Add(s, l, r) if t == what && u.intersect(BindingAssessment.freeVariables(t)).isEmpty => repl
      case Subtract(s, l, r) if t != what => Subtract(s, usubst(o, u, l), usubst(o, u, r))
      case Subtract(s, l, r) if t == what && u.intersect(BindingAssessment.freeVariables(t)).isEmpty => repl
      case Multiply(s, l, r) if t != what => Multiply(s, usubst(o, u, l), usubst(o, u, r))
      case Multiply(s, l, r) if t == what && u.intersect(BindingAssessment.freeVariables(t)).isEmpty => repl
      case Divide(s, l, r) if t != what => Divide(s, usubst(o, u, l), usubst(o, u, r))
      case Divide(s, l, r) if t == what && u.intersect(BindingAssessment.freeVariables(t)).isEmpty => repl
      case Exp(s, l, r) if t != what => Exp(s, usubst(o, u, l), usubst(o, u, r))
      case Exp(s, l, r) if t == what && u.intersect(BindingAssessment.freeVariables(t)).isEmpty => repl
      case Pair(dom, l, r) if t != what => Pair(dom, usubst(o, u, l), usubst(o, u, r))
      case Pair(dom, l, r) if t == what && u.intersect(BindingAssessment.freeVariables(t)).isEmpty => repl
      // base cases
      case x: Variable if !u.contains(x) && x == what => repl
      case x: Variable if  u.contains(x) || x != what => x
      case d: Derivative if d == what => repl
      case Derivative(s, e) if e == what => Derivative(s, repl)
      case Derivative(_, e) if e != what => t
      case app@Apply(fn, theta) if !u.contains(fn) && app == what => repl
      case app@Apply(fn, theta) if  u.contains(fn) || app != what => Apply(fn, usubst(o, u, theta))
      case Nothing => Nothing
      case Number(_, _) if t == what => repl
      case x: Atom => x
      case _ => throw new UnknownOperatorException("Not implemented yet", t)
    }
  }

  private def usubst(o: SetLattice[NamedSymbol], u: SetLattice[NamedSymbol], f: Formula): Formula = f match {
    // homomorphic cases
    case Not(g) => Not(usubst(o, u, g))
    case And(l, r) => And(usubst(o, u, l), usubst(o, u, r))
    case Or(l, r) => Or(usubst(o, u, l), usubst(o, u, r))
    case Imply(l, r) => Imply(usubst(o, u, l), usubst(o, u, r))
    case Equiv(l, r) => Equiv(usubst(o, u, l), usubst(o, u, r))

    case Equals(d, l, r) => Equals(d, usubst(o, u, l), usubst(o, u, r))
    case NotEquals(d, l, r) => NotEquals(d, usubst(o, u, l), usubst(o, u, r))
    case GreaterEqual(d, l, r) => GreaterEqual(d, usubst(o, u, l), usubst(o, u, r))
    case GreaterThan(d, l, r) => GreaterThan(d, usubst(o, u, l), usubst(o, u, r))
    case LessEqual(d, l, r) => LessEqual(d, usubst(o, u, l), usubst(o, u, r))
    case LessThan(d, l, r) => LessThan(d, usubst(o, u, l), usubst(o, u, r))

    // binding cases add bound variables to u
    case Forall(vars, g) => Forall(vars, usubst(o ++ vars, u ++ vars, g))
    case Exists(vars, g) => Exists(vars, usubst(o ++ vars, u ++ vars, g))

    case BoxModality(p, g) => val USR(q, v, sp) = usubst(o, u, p); BoxModality(sp, usubst(q, v, g))
    case DiamondModality(p, g) => val USR(q, v, sp) = usubst(o, u, p); DiamondModality(sp, usubst(q, v, g))

    // uniform substitution base cases
    case ApplyPredicate(fn, theta) => ApplyPredicate(fn, usubst(o, u, theta))
    case FormulaDerivative(g) => FormulaDerivative(usubst(o, u, g))
    case x: Atom => x
    case _ => throw new UnknownOperatorException("Not implemented yet", f)
  }

  private def usubst(o: SetLattice[NamedSymbol], u: SetLattice[NamedSymbol], p: Program): USR = p match {
    case Assign(x: Variable, e) => USR(o+x, u+x, Assign(x, usubst(o, u, e)))
    case Assign(d@Derivative(_, x: Variable), e) => USR(o+x, u+x, Assign(d, usubst(o, u, e)))
    case NDetAssign(x: Variable) => USR(o+x, u+x, p)
    case Test(f) => USR(o, u, Test(usubst(o, u, f)))
    case IfThen(cond, thenT) => USR(o, u, IfThen(usubst(o,u,cond), thenT)) //@todo eisegesis.
    case ode: DifferentialProgram => val x = primedVariables(ode); val sode = usubst(o, u, x, ode); USR(o++SetLattice(x), u++SetLattice(x), sode)
    case Sequence(a, b) => val USR(q, v, as) = usubst(o, u, a); val USR(r, w, bs) = usubst(q, v, b); USR(r, w, Sequence(as, bs))
    case Choice(a, b) =>
      val USR(q, v, as) = usubst(o, u, a); val USR(r, w, bs) = usubst(o, u, b)
      USR(q.intersect(r), v++w, Choice(as, bs))
    case Loop(a) => val USR(q, v, _) = usubst(o, u, a); val USR(r, w, as) = usubst(o, v, a); USR(o, w, Loop(as))
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
  private def usubst(o: SetLattice[NamedSymbol], u: SetLattice[NamedSymbol], primed: Set[NamedSymbol], p: DifferentialProgram):
      DifferentialProgram = p match {
    case ODEProduct(a, b) => ODEProduct(usubst(o, u, primed, a), usubst(o, u, primed, b))
    case ODESystem(d, a, h) if d.isEmpty => ODESystem(d, usubst(o, u, primed, a), usubst(o++SetLattice(primed), u++SetLattice(primed), h))
    case ODESystem(d, _, _) if d.nonEmpty => throw new UnknownOperatorException("Check implementation whether passing v is correct.", p)
    case AtomicODE(d@Derivative(_, x: Variable), e) => AtomicODE(d, usubst(o++SetLattice(primed), u++SetLattice(primed), e))
    case _: EmptyODE => p
    case IncompleteSystem(s) => IncompleteSystem(usubst(o, u, primed, s))
    case CheckedContEvolveFragment(s) => CheckedContEvolveFragment(usubst(o, u, primed, s))
  }
}
