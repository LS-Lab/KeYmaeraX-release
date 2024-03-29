/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */

package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, PositionLocator}
import edu.cmu.cs.ls.keymaerax.parser.Declaration

import scala.collection.immutable.{List, Seq}

/** Empty placeholder, ignores tactics. */
object MockExpressionBuilder extends ((String, List[Either[Seq[Any], PositionLocator]], Declaration) => BelleExpr) {

  /** Parses tactic string `t` with inputs and positions `in` and  */
  override def apply(t: String, in: List[Either[Seq[Any], PositionLocator]], defs: Declaration): BelleExpr = {
    //@todo check that tactic string `t` is an implemented tactic
    new BelleExpr()
  }

}
