/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.{And, DotTerm, Equal, Forall, FuncOf, Function, Greater, Imply, Number, Real, Tuple, Unit, Variable}

/** List of built-in interpreted function symbols. */
object InterpretedSymbols {
  val maxF: Function = Function("max", None, Tuple(Real, Real), Real,
    interp = Some(Parser.parser.formulaParser("(._1 < ._2 & ._0 = ._2) | (._1 >= ._2 & ._0 = ._1)")))

  val minF: Function = Function("min", None, Tuple(Real, Real), Real,
    interp = Some(Parser.parser.formulaParser("(._1 < ._2 & ._0 = ._1) | (._1 >= ._2 & ._0 = ._2)")))

  val absF: Function = Function("abs", None, Real, Real,
    interp = Some(Parser.parser.formulaParser("(._1 < 0 & ._0 = -(._1)) | (._1 >= 0 & ._0 = ._1)")))

  val expF: Function = ODEToInterpreted.fromProgram(Parser.parser.programParser("{exp:=1;}; {exp'=exp}"), Variable("t")).head

  // Define E as exp(1)
  val E: Function = Function("e",None,Unit,Real,interp = Some(Equal(DotTerm(idx=Some(0)),FuncOf(expF,Number(1)))))

  val (sinF, cosF) = {
    val fns = ODEToInterpreted.fromProgram(
      Parser.parser.programParser("{sin:=0;cos:=1;}; {sin'=cos, cos'=-sin}"), Variable("t"))
    (fns(0), fns(1))
  }

  // Define PI as unique y s.t. y > 0 & sin(y) = 0 & forall 0 < x < y, sin(x) > 0
  val PI: Function = Function("pi",None,Unit,Real,interp = Some(
    And(Parser.parser.formulaParser("._0 > 0"),
    And( Equal(FuncOf(sinF,DotTerm(idx=Some(0))), Number(0)),
         Forall(Variable("x_") :: Nil, Imply(Parser.parser.formulaParser("0 < x_ & x_ < ._0"),
          Greater(FuncOf(sinF,Variable("x_")),Number(0))
         ))
    ))))

  /** The builtin interpreted function symbols. */
  val builtin: List[Function] = List(
    absF,
    minF,
    maxF,
    expF,
    sinF,
    cosF,
    PI
  ) ensures(r => r.forall(f => f.interpreted), "only interpreted symbols are interpreted")

  /** The nondifferentiable builtin interpreted function symbols. */
  val nondiffBuiltin: List[Function] = List(
    absF,
    minF,
    maxF,
    PI
  ) ensures(r => r.forall(f => f.interpreted), "only interpreted symbols are interpreted")

  /** The interpreted symbols by name. */
  val byName: Map[(String, Option[Int]),Function] = builtin.map(f => (f.name, f.index) -> f).toMap
}
