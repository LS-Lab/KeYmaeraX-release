/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.{NonSubstUnificationMatch, Position}
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
  type Generator[A] = ((Sequent, Position) => Stream[A])
}

/** Generator always providing a fixed list as output. */
case class FixedGenerator[A](list: List[A]) extends Generator.Generator[A] {
  def apply(s: Sequent, p: Position): Stream[A] = list.toStream
}

/** Map-based generator providing output according to the fixed map `products` according to its program or whole formula.
  * @author Stefan Mitsch
  * */
class ConfigurableGenerator[A](var products: Map[Expression,Seq[A]] = Map[Expression,Seq[A]]()) extends Generator.Generator[A] {
  def apply(s: Sequent, p: Position): Stream[A] = s.sub(p) match {
    case Some(Box(prg, _)) => findPrgProducts(prg)
    case Some(Diamond(prg, _)) => findPrgProducts(prg)
    case Some(f) => products.getOrElse(f, Nil).toStream
    case None => Nil.toStream
  }

  /** Finds products that match the program `prg` either literally, or if ODE then without evolution domain constraint. */
  private def findPrgProducts(prg: Program): Stream[A] = prg match {
    case sys@ODESystem(ode, _) =>
      products.find({ case (ODESystem(key, _), _) => ode == key case _ => false }).
        getOrElse(() -> findConditionalDiffInv(sys))._2.toStream
    case _ => products.getOrElse(prg, Nil).toStream
  }

  /** Finds products that match the ODE `ode` by shape and with a condition that matches.
    * For example, v'=A matches v'=a@invariant(v'=A->v>=old(v), v'=-2 -> v<=old(v)). */
  private def findConditionalDiffInv(ode: ODESystem): Seq[A] = {
    //@note UnificationMatch and RenUSubst won't allow numbers, use own naive subst in these cases
    products.find({
        case (ODESystem(key, _), _) =>
          val subs = Try(NonSubstUnificationMatch.unifyODE(key, ode.ode)).toOption.getOrElse(Nil)
          NonSubstUnificationMatch.unifier(subs)(key) == ode.ode
        case _ => false
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
}
