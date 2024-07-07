/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package org.keymaerax.parser

import org.keymaerax.bellerophon.{BelleExpr, PositionLocator}
import org.keymaerax.parser.Declaration

import scala.collection.immutable.{List, Seq}

/** Empty placeholder, ignores tactics. */
object MockBellePrettyPrinter extends (BelleExpr => String) {

  override def apply(t: BelleExpr): String = ""

}
