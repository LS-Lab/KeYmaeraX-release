/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, PositionLocator}
import edu.cmu.cs.ls.keymaerax.parser.Declaration

import scala.collection.immutable.{List, Seq}

/** Empty placeholder, ignores tactics. */
object MockBellePrettyPrinter extends (BelleExpr => String) {

  override def apply(t: BelleExpr): String = ""

}
