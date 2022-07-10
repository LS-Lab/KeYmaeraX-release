/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.pt

import edu.cmu.cs.ls.keymaerax.core._
import scala.collection.immutable

trait ProvableSig {
  val subgoals: immutable.IndexedSeq[Sequent]
}