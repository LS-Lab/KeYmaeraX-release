/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{Function, Real, Tuple}

/** Lists interpreted function symbols. */
object InterpretedSymbols {
  val maxF: Function = Function("max", None, Tuple(Real, Real), Real, interpreted = true)
  val minF: Function = Function("min", None, Tuple(Real, Real), Real, interpreted = true)
  val absF: Function = Function("abs", None, Real, Real, interpreted = true)

  /** The interpreted function symbols. */
  val symbols: List[Function] = List(
      absF,
      minF,
      maxF,
  ) ensures(r => r.forall(f => f.interpreted), "only interpreted symbols are interpreted")

  /** The interpreted symbols by name. */
  val byName: Map[(String, Option[Int]),Function] = symbols.map(f => (f.name, f.index) -> f).toMap
}
