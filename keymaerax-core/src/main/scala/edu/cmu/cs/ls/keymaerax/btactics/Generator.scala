/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.Position

/**
 * Created by smitsch on 12/23/14.
 */

/**
 * Invariant generators etc, where `apply` results in an iterator over objects of type `A` to try.
 * Results do not necessarily have to be deterministic.
  * @tparam A the type of results that are being generated.
  * @author Stefan Mitsch
 */
trait Generator[A] extends ((Sequent, Position) => Iterator[A])

/** Generatora lways providing a fixed list as output. */
case class FixedGenerator[A](list: List[A]) extends Generator[A] {
  def apply(s: Sequent, p: Position) = list.iterator
}

/** Map-based generator providing output according to the fixed map `product` according to its program or whole formula.
  * @author Stefan Mitsch
  * */
class ConfigurableGenerator[A](var products: Map[Expression,A] = Map[Expression,A]()) extends Generator[A] {
  //@todo why p.top instead of p?
  def apply(s: Sequent, p: Position): Iterator[A] = s(p.top) match {
    case Box(prg, _) => products.get(prg).iterator
    case Diamond(prg, _) => products.get(prg).iterator
    case _ => products.get(s(p.top)).iterator
  }
}