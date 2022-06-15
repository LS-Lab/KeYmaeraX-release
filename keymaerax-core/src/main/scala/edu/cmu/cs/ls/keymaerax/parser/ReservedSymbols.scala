/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core._

/** List of reserved symbols. */
object ReservedSymbols {
  val exerciseP: UnitPredicational = UnitPredicational("exerciseP_", AnyArg)
  val exerciseF: UnitFunctional = UnitFunctional("exerciseF_", AnyArg, Real)
  val exerciseS: SystemConst = SystemConst("exerciseS_", AnyArg)
  val exerciseD: DifferentialProgramConst = DifferentialProgramConst("exerciseD_", AnyArg)

  /** The builtin reserved symbols. */
  val reserved: List[NamedSymbol] = List(
    exerciseF,
    exerciseP,
    exerciseS,
    exerciseD
  )

  /** The reserved symbols by name. */
  val byName: Map[(String, Option[Int]), NamedSymbol] = reserved.map(f => (f.name, f.index) -> f).toMap
}
