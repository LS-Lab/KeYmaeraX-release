/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.pt

import org.keymaerax.core._
import scala.collection.immutable

trait ProvableSig {
  val subgoals: immutable.IndexedSeq[Sequent]
}
