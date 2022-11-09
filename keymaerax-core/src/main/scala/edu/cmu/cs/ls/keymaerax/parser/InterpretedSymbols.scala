/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.parser

import edu.cmu.cs.ls.keymaerax.core.Function

import scala.io.Source

/** List of pre-shipped interpreted function symbols. */
object InterpretedSymbols {
  /** The pre-shipped math.kyx definitions. */
  lazy val mathKyxDefs: Declaration = {
    val builtin = getClass.getResourceAsStream("/kyx/math.kyx")
    val packageContent = Source.fromInputStream(builtin).mkString
    ArchiveParser.definitionsPackageParser(packageContent)
  }

  lazy val preshipped: Declaration = mathKyxDefs

  /** Reads definition `defName` from the builtin definitions file. */
  private def read(defName: String): Function = {
    mathKyxDefs.asNamedSymbols.find(_.name == defName).get.asInstanceOf[Function]
  }

  lazy val maxF: Function = read("max")
  lazy val minF: Function = read("min")
  lazy val absF: Function = read("abs")
  lazy val expF: Function = read("exp")
  lazy val E: Function    = read("e")
  lazy val sinF: Function = read("sin")
  lazy val cosF: Function = read("cos")
  lazy val PI: Function   = read("pi")

  /** The nondifferentiable builtin interpreted function symbols (all << fml >>-defined functions
   * because don't know anything about the shape of fml). */
  lazy val nondiffBuiltin: List[Function] = Declaration(
    mathKyxDefs.decls.filter({ case (_, Signature(_, _, _, Left(_), _)) => true case _ => false })).
      asNamedSymbols.flatMap({ case f: Function => Some(f) case _ => None })
}
