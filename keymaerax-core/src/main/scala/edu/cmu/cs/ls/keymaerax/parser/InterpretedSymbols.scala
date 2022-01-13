/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{Function, Real, Tuple}

import scala.collection.immutable.Vector

/** List of built-in interpreted function symbols. */
object InterpretedSymbols {
  val maxF: Function = Function("max", None, Tuple(Real, Real), Real,
    interp = Some(Parser.parser.formulaParser("(._1 < ._2 & ._0 = ._2) | (._1 >= ._2 & ._0 = ._1)")))

  val minF: Function = Function("min", None, Tuple(Real, Real), Real,
    interp = Some(Parser.parser.formulaParser("(._1 < ._2 & ._0 = ._1) | (._1 >= ._2 & ._0 = ._2)")))

  val absF: Function = Function("abs", None, Real, Real,
    interp = Some(Parser.parser.formulaParser("(._1 < 0 & ._0 = -(._1)) | (._1 >= 0 & ._0 = ._1)")))

  val expF: Function = ODEToInterpreted.fromProgram(Parser.parser.programParser("{exp:=1;}; {exp'=exp}")).head

  val (sinF, cosF) = {
    val fns = ODEToInterpreted.fromProgram(
      Parser.parser.programParser("{sin:=0;cos:=1;}; {sin'=cos, cos'=-sin}"))
    (fns(0), fns(1))
  }

  /** The interpreted function symbols. */
  val symbols: List[Function] = List(
    absF,
    minF,
    maxF,
    expF,
    sinF,
    cosF
  ) ensures(r => r.forall(f => f.interpreted), "only interpreted symbols are interpreted")

  /** The interpreted symbols by name. */
  val byName: Map[(String, Option[Int]),Function] = symbols.map(f => (f.name, f.index) -> f).toMap
}
