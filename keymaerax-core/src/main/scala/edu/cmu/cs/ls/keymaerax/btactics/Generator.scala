/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.Position
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._

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

/** Map-based generator providing output according to the fixed map `product` according to its program or whole formula.
  * @author Stefan Mitsch
  * */
class ConfigurableGenerator[A](var products: Map[Expression,A] = Map[Expression,A]()) extends Generator.Generator[A] {
  def apply(s: Sequent, p: Position): Iterator[A] = s.sub(p) match {
    case Some(Box(prg, _)) => products.get(prg).iterator
    case Some(Diamond(prg, _)) => products.get(prg).iterator
    case Some(f) => products.get(f).iterator
    case None => Nil.iterator
  }
}