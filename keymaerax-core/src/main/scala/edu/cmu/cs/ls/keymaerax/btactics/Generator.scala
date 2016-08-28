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
 * Invariant generators etc, where `apply` results in an object of type `A` to try.
 * Results do not have to be deterministic, e.g., calls to apply might advance to the next candidate.
  * @todo change to (Sequent,Position) => Iterator[A] maybe?
  * @todo add implementation for something like (Sequent, Position) => Stream[A] for example?
  * @tparam A the type of results that are being generated.
  * @author Stefan Mitsch
 */
trait Generator[A] extends ((Sequent, Position) => Option[A]) {
  def peek(s: Sequent, p: Position): Option[A]
}

/** Singleton generator only providing a single fixed output `f` every time it is asked. */
class Generate[A](f: A) extends Generator[A] {
  def apply(s: Sequent, p: Position) = Some(f)
  def peek(s: Sequent, p: Position) = Some(f)
}

/** Empty generator never providing any output */
class NoneGenerate[A] extends Generator[A] {
  def apply(s: Sequent, p: Position) = None
  def peek(s: Sequent, p: Position) = None
}

/** Map-based generator providing output according to the fixed map `product` according to its program or whole formula.
  * @author Stefan Mitsch
  * */
class ConfigurableGenerate[A](var products: Map[Expression,A] = Map[Expression,A]()) extends Generator[A] {
  //@todo why p.top instead of p?
  def apply(s: Sequent, p: Position) = s(p.top) match {
    case Box(prg, _) => products.get(prg)
    case Diamond(prg, _) => products.get(prg)
    case _ => products.get(s(p.top))
  }
  def peek(s: Sequent, p: Position) = s(p.top) match {
    case Box(prg, _) => products.get(prg)
    case Diamond(prg, _) => products.get(prg)
    case _ => products.get(s(p.top))
  }
}