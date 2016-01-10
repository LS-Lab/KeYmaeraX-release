/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.bellerophon.Position

/**
 * Created by smitsch on 12/23/14.
 * @author Stefan Mitsch
 */

/**
 * apply results in a formula to try.
 * Results do not have to be deterministic, e.g., calls to apply might advance to the next candidate.
 * Results can also be deterministic.
  * @todo change to (Sequent,Position) => Iterator[A] maybe?
  * @todo add implementation for something like (Sequent, Position) => Stream[A] for example?
 */
trait Generator[A] extends ((Sequent, Position) => Option[A]) {
  def peek(s: Sequent, p: Position): Option[A]
}

class Generate[A](f: A) extends Generator[A] {
  def apply(s: Sequent, p: Position) = Some(f)
  def peek(s: Sequent, p: Position) = Some(f)
}

class NoneGenerate[A] extends Generator[A] {
  def apply(s: Sequent, p: Position) = None
  def peek(s: Sequent, p: Position) = None
}

class ConfigurableGenerate[A](var products: Map[Expression,A] = Map[Expression,A]()) extends Generator[A] {
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