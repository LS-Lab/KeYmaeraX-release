/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.{FreshUnificationMatch, Position, RenUSubst}
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper

import scala.util.Try

/** Invariant generator
  * @author Stefan Mitsch
  * */
object Generator {
  /**
    * Invariant generators etc, where `apply` results in an iterator over objects of type `A` to try.
    * Results do not necessarily have to be deterministic.
    * @tparam A the type of results that are being generated.
    * @author Stefan Mitsch
    */
  type Generator[A] = ((Sequent, Position) => Iterator[A])
}

/** Generator always providing a fixed list as output. */
case class FixedGenerator[A](list: List[A]) extends Generator.Generator[A] {
  def apply(s: Sequent, p: Position): Iterator[A] = list.iterator
}

/** Map-based generator providing output according to the fixed map `products` according to its program or whole formula.
  * @author Stefan Mitsch
  * */
class ConfigurableGenerator[A](var products: Map[Expression,Seq[A]] = Map[Expression,Seq[A]]()) extends Generator.Generator[A] {
  def apply(s: Sequent, p: Position): Iterator[A] = s.sub(p) match {
    case Some(Box(prg, _)) => findPrgProducts(prg)
    case Some(Diamond(prg, _)) => findPrgProducts(prg)
    case Some(f) => products.getOrElse(f, Nil).iterator
    case None => Nil.iterator
  }

  /** Finds products that match the program `prg` either literally, or if ODE then without evolution domain constraint. */
  private def findPrgProducts(prg: Program): Iterator[A] = prg match {
    case sys@ODESystem(ode, _) =>
      products.find({ case (ODESystem(key, _), _) => ode == key case _ => false }).
        getOrElse(() -> findConditionalDiffInv(sys))._2.iterator
    case _ => products.getOrElse(prg, Nil).iterator
  }

  /** Finds products that match the ODE `ode` by shape and with a condition that matches.
    * For example, v'=A matches v'=a@invariant(v'=A->v>=old(v), v'=-2 -> v<=old(v)). */
  private def findConditionalDiffInv(ode: ODESystem): Seq[A] = {
    //@note UnificationMatch and RenUSubst won't allow numbers, use own naive subst in these cases
    products.find({
        case (ODESystem(key, _), _) =>
          val subs = Try(GeneratorUnificationMatch.unifyODE(key, ode.ode)).toOption.getOrElse(Nil)
          unifier(subs)(key) == ode.ode
      }).map({ case (_, odeProducts) =>
        odeProducts.map({
          case Imply(Equal(xp: DifferentialSymbol, e), invCandidate) =>
            if (DifferentialHelper.atomicOdes(ode.ode).exists(a => a.xp == xp && a.e == e)) {
              Some(invCandidate.asInstanceOf[A])
            } else None
          case inv => Some(inv)
        })
      }).getOrElse(Nil).filter(_.isDefined).map(_.get).distinct
  }

  /** Returns either a standard RenUSubst or the naive unifier. */
  private def unifier(subs: List[(Expression, Expression)]): (Expression => Expression) = {
    val distinct = subs.distinct
    Try(RenUSubst(distinct)).toOption.getOrElse(NaiveSubst(distinct))
  }

  /** Naive substitution for unsupported RenUSubst cases (numbers for variables etc.) */
  private case class NaiveSubst(subs: List[(Expression, Expression)]) extends (Expression => Expression) {
    def apply(e: Expression): Expression = e match {
      case prg: Program => subs.foldLeft(prg)({ case (p, (what: Term, repl: Term)) => p.replaceFree(what, repl) })
      case fml: Formula => subs.foldLeft(fml)({ case (p, (what: Term, repl: Term)) => p.replaceFree(what, repl) })
      case trm: Term => subs.foldLeft(trm)({ case (p, (what: Term, repl: Term)) => p.replaceFree(what, repl) })
    }
  }

  /** Unify any term for variables in ODEs. */
  private object GeneratorUnificationMatch extends FreshUnificationMatch {
    //@note Overriding additional unify... and other methods might become necessary,
    // since FreshUnificationMatch.apply attempts to create RenUSubst, which will fail in the usual unsupported cases
    // (numbers for variables etc.)

    override def unifyODE(e1: DifferentialProgram, e2: DifferentialProgram): List[(Expression, Expression)] = super.unifyODE(e1, e2)

    override def unifies(s1: Term, s2: Term, t1: Term, t2: Term): List[SubstRepl] = {
      val u1 = unify(s1, t1)
      try {
        compose(unify(ConfigurableGenerator.this.unifier(u1)(s2), t2), u1)
      } catch {
        case e: ProverException =>
          logger.trace("      try converse since " + e.getMessage)
          val u2 = unify(s2, t2)
          compose(unify(t1, ConfigurableGenerator.this.unifier(u2)(s1)), u2)
      }
    }

    override def unifies(s1: Formula, s2: Formula, t1: Formula, t2: Formula): List[SubstRepl] = {
      val u1 = unify(s1, t1)
      try {
        compose(unify(ConfigurableGenerator.this.unifier(u1)(s2), t2), u1)
      } catch {
        case e: ProverException =>
          logger.trace("      try converse since " + e.getMessage)
          val u2 = unify(s2, t2)
          compose(unify(t1, ConfigurableGenerator.this.unifier(u2)(s1)), u2)
      }
    }

    override def unifies(s1: Program, s2: Program, t1: Program, t2: Program): List[SubstRepl] = {
      val u1 = unify(s1, t1)
      try {
        compose(unify(ConfigurableGenerator.this.unifier(u1)(s2), t2), u1)
      } catch {
        case e: ProverException =>
          logger.trace("      try converse since " + e.getMessage)
          val u2 = unify(s2, t2)
          compose(unify(t1, ConfigurableGenerator.this.unifier(u2)(s1)), u2)
      }
    }

    override def unifiesODE(s1: DifferentialProgram, s2: DifferentialProgram, t1: DifferentialProgram,
                            t2: DifferentialProgram): List[SubstRepl] = {
      val u1 = unifyODE(s1, t1)
      try {
        compose(unifyODE(ConfigurableGenerator.this.unifier(u1)(s2).asInstanceOf[DifferentialProgram], t2), u1)
      } catch {
        case _: ProverException =>
          val u2 = unifyODE(s2, t2)
          compose(unifyODE(t1, ConfigurableGenerator.this.unifier(u2)(s1).asInstanceOf[DifferentialProgram]), u2)
      }
    }

    override def compose(after: List[SubstRepl], before: List[SubstRepl]): List[SubstRepl] =
      before ++ transpose(before, after)

    private def transpose(repl: List[SubstRepl], input: List[SubstRepl]): List[SubstRepl] = {
      val ren = repl.filter({ case (_: BaseVariable, _: BaseVariable) => true case _ => false }).map(_.swap)
      if (ren.isEmpty) input
      else {
        val ur = ConfigurableGenerator.this.unifier(ren)
        input.map(sp => (sp._1, ur(sp._2))).filter(sp => sp._1 != sp._2)
      }
    }

    override def unifyVar(x1: Variable, e2: Expression): List[(Expression, Expression)] =
      if (x1==e2) id
      else unifier(x1, e2)
  }
}
