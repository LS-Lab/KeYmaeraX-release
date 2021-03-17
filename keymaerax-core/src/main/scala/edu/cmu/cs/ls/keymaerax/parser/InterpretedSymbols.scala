package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{Function, Real, Tuple}

/** Lists interpreted function symbols. */
object InterpretedSymbols {
  val maxF: Function = Function("max", None, Tuple(Real, Real), Real, interpreted = true)
  val minF: Function = Function("min", None, Tuple(Real, Real), Real, interpreted = true)
  val absF: Function = Function("abs", None, Real, Real, interpreted = true)
}
