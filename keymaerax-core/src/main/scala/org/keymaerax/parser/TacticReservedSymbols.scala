/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.parser

import org.keymaerax.core.{Function, Real, Unit}

/** Lists function symbols that have special meaning in tactics. */
object TacticReservedSymbols {
  val old: Function = Function("old", None, Real, Real, None)
  val abbrv: Function = Function("abbrv", None, Real, Real, None)
  val expand: Function = Function("expand", None, Real, Real, None)
  val const: Function = Function("const", None, Unit, Real, None)

  /** The reserved function symbols. */
  val symbols: List[Function] = List(old, abbrv, expand, const) ensures
    (r => r.forall(f => !f.interpreted), "reserved symbols are not interpreted")

  /** The reserved symbols by name. */
  val byName: Map[(String, Option[Int]), Function] = symbols.map(f => (f.name, f.index) -> f).toMap

  /** The reserved symbols definitions. */
  val asDecl: Declaration = Declaration(byName.map({ case ((n, i), fn) =>
    Name(n, i) -> Signature(Some(fn.domain), fn.sort, None, Right(None), UnknownLocation)
  }))
}
