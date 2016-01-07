/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.tactics

import edu.cmu.cs.ls.keymaerax.core._

/**
 * Created by smitsch on 12/23/14.
 * @author Stefan Mitsch
 */

/**
 * apply results in a formula to try.
 * Results do not have to be deterministic, e.g., calls to apply might advance to the next candidate.
 * Results can also be deterministic.
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
  def apply(s: Sequent, p: Position) = s.apply(p) match {
    case Box(prg, _) => products.get(prg)
    case Diamond(prg, _) => products.get(prg)
    case _ => products.get(s.apply(p))
  }
  def peek(s: Sequent, p: Position) = s.apply(p) match {
    case Box(prg, _) => products.get(prg)
    case Diamond(prg, _) => products.get(prg)
    case _ => products.get(s.apply(p))
  }
}