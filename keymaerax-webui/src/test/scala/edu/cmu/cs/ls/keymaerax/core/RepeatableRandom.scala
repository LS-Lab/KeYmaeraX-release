/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.btactics.RandomFormula

import scala.util.Random
import scala.collection.immutable
import scala.collection.immutable._

/**
 * Repeatable random number generator for testing purposes. Each use of RandomFormula will print a random seed with
 * which the same random tests can be repeated.
 * {{{
 *   val randRoot = RepeatableRandom()
 *   // will print something like RepeatableRandom(-4317240407825764493L) on screen
 *   // The same sequence of pseudo-random numbers can, thus, be regenerated again from
 *   val sameRand = RepeatableRandom(-4317240407825764493L)
 *   val rand = randRoot.nextFormulaEpisode()
 * }}}
 *
 * @author
 *   Andre Platzer
 * @param seed
 *   the random seed, for repeatable random testing purposes.
 */
class RepeatableRandom(val seed: Long = new Random().nextLong()) {
//  println("regenerate by RepeatableRandom(" + seed + "L)")
  val rand: Random = new Random(seed)

  /** next Random episode */
  def nextEpisode(): Random = new Random(rand.nextLong())

  /** next RandomFormula episode */
  def nextFormulaEpisode(): RandomFormula = { print("episode "); new RandomFormula(rand.nextLong()) }

  /** next Long */
  def nextLong(): Long = rand.nextLong()
}

object RepeatableRandom {
  def apply() = new RepeatableRandom()
  def apply(seed: Long) = new RepeatableRandom(seed)
}
