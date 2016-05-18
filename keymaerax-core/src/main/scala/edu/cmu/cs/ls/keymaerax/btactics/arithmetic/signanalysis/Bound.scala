/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.arithmetic.signanalysis

import edu.cmu.cs.ls.keymaerax.core._

/** Directionality arithmetic.
  * @author Stefan Mitsch
  */
object Bound extends Enumeration {
  type Direction = Value
  val Less, LessEqual, Equal, GreaterEqual, Greater, Unknown = Value


}