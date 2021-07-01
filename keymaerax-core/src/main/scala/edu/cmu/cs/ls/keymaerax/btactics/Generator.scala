/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors._
import edu.cmu.cs.ls.keymaerax.btactics.helpers.DifferentialHelper
import edu.cmu.cs.ls.keymaerax.infrastruct.{NonSubstUnificationMatch, Position, UnificationMatch}
import edu.cmu.cs.ls.keymaerax.parser.Declaration

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
  type Generator[A] = (Sequent, Position) => Stream[A]
}

/** Generator always providing a fixed list as output. */
case class FixedGenerator[A](list: List[A]) extends Generator.Generator[A] {
  def apply(s: Sequent, p: Position): Stream[A] = list.toStream
}

object ConfigurableGenerator {
  /** Creates a generator that has `products` in verbatim form and fully expanded according to defs`. */
  def create[A](products: Map[Expression, Seq[A]], defs: Declaration): ConfigurableGenerator[A] = new ConfigurableGenerator[A](
    products.map({ case (k, v) =>
      defs.elaborateToSystemConsts(defs.elaborateToFunctions(k)) ->
        v.map({
          case (f: Expression, h) => defs.elaborateToSystemConsts(defs.elaborateToFunctions(f)) -> h
          case v => v
        }).distinct
    }).asInstanceOf[Map[Expression, Seq[A]]] ++
    products.map({ case (k, v) =>
      defs.exhaustiveSubst(defs.elaborateToSystemConsts(defs.elaborateToFunctions(k))) ->
        v.map({
          case (f: Expression, h) => defs.exhaustiveSubst(defs.elaborateToSystemConsts(defs.elaborateToFunctions(f))) -> h
          case v => v
        }).distinct
    }).asInstanceOf[Map[Expression, Seq[A]]]
  )
}

/** Map-based generator providing output according to the fixed map `products` according to its program or whole formula.
  * @author Stefan Mitsch
  * */
class ConfigurableGenerator[A](var products: Map[Expression,Seq[A]] = Map[Expression,Seq[A]]()) extends Generator.Generator[A] {
  def apply(s: Sequent, p: Position): Stream[A] = s.sub(p) match {
    case Some(Box(prg, _)) => findPrgProducts(prg)
    case Some(Diamond(prg, _)) => findPrgProducts(prg)
    case Some(f) => products.getOrElse(f, Nil).distinct.toStream
    case None => Nil.toStream
  }

  /** Finds products that match the program `prg` either literally, or if ODE then without evolution domain constraint. */
  private def findPrgProducts(prg: Program): Stream[A] = prg match {
    case sys@ODESystem(ode, _) =>
      val odeProducts = products.find({ case (ODESystem(key, _), _) => ode == key case _ => false })
      val extractedConditionalProducts = odeProducts.map(p => (
        p._1,
        p._2.map(extractConditionalDiffInv(DifferentialHelper.atomicOdes(p._1.asInstanceOf[ODESystem]), _)).
          filter(_.isDefined).flatten))
      extractedConditionalProducts.getOrElse(() -> findConditionalDiffInv(sys))._2.distinct.toStream
    case _ => products.get(prg) match {
      case Some(products) => products.distinct.toStream
      case None => products.find({ case (k, _) => Try(!UnificationMatch(k, prg).isEmpty).getOrElse(false) }) match {
        case Some((_, products)) => products.distinct.toStream
        case None => Nil.toStream
      }
    }
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
        odeProducts.map(extractConditionalDiffInv(DifferentialHelper.atomicOdes(ode.ode), _))
      }).getOrElse(Nil).filter(_.isDefined).flatten.distinct
  }

  /** Extracts the right-hand side of a conditional differential invariant. */
  private def extractConditionalDiffInv(odeAtoms: List[AtomicODE], product: A): Option[A] = product match {
    case (Imply(Equal(xp: DifferentialSymbol, e), invCandidate), hint) =>
      if (odeAtoms.exists(a => a.xp == xp && a.e == e)) {
        Some((invCandidate, hint).asInstanceOf[A])
      } else None
    case _ => Some(product)
  }
}
