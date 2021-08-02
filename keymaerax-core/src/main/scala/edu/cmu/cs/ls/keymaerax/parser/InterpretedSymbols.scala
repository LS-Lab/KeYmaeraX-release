/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{And, DotTerm, Equal, Function, GreaterEqual, Less, Neg, Number, Or, Real, Tuple}

/** Lists interpreted function symbols. */
object InterpretedSymbols {
  val maxF: Function = Function("max", None, Tuple(Real, Real), Real,
    interp = Some(Or(
                And(Less(DotTerm(idx=Some(0)),DotTerm(idx=Some(1))),         Equal(DotTerm(), DotTerm(idx=Some(1)))),
                And(GreaterEqual(DotTerm(idx=Some(0)),DotTerm(idx=Some(1))), Equal(DotTerm(), DotTerm(idx=Some(0))))
              )))
  val minF: Function = Function("min", None, Tuple(Real, Real), Real,
    interp = Some(Or(
      And(Less(DotTerm(idx=Some(0)),DotTerm(idx=Some(1))),         Equal(DotTerm(), DotTerm(idx=Some(0)))),
      And(GreaterEqual(DotTerm(idx=Some(0)),DotTerm(idx=Some(1))), Equal(DotTerm(), DotTerm(idx=Some(1))))
    )))
  val absF: Function = Function("abs", None, Real, Real,
    interp = Some(Or(
      And(GreaterEqual(DotTerm(idx=Some(0)),Number(0)),Equal(DotTerm(),DotTerm(idx=Some(0)))),
      And(Less(DotTerm(idx=Some(0)),Number(0)), Equal(DotTerm(), Neg(DotTerm(idx=Some(0)))))
    )))

  /** The interpreted function symbols. */
  val symbols: List[Function] = List(
      absF,
      minF,
      maxF,
  ) ensures(r => r.forall(f => f.interpreted), "only interpreted symbols are interpreted")

  /** The interpreted symbols by name. */
  val byName: Map[(String, Option[Int]),Function] = symbols.map(f => (f.name, f.index) -> f).toMap
}
