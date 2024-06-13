/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.cli

import edu.cmu.cs.ls.keymaerax.btactics.macros._
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration
import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}

object DerivationInfoPrinter {

  def main(args: Array[String]): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    try {
      KeymaeraxCore.initializeProver(ToolConfiguration())
      val out = DerivationInfo
        .allInfo
        .map({ case (k, v) => (k, v.persistentInputs, v.numPositionArgs) })
        .map({ case (codeName, argInfo, numPosArgs) =>
          s"""case "$codeName" => DerivationInfo("$codeName", ${printArgInfo(argInfo)}, $numPosArgs)"""
        })
        .mkString("\n") + "\ncase t => throw ParseException(\"Unknown tactic \" + t)"
      println(out)
    } finally { KeymaeraxCore.shutdownProver() }
  }

  private def printArgInfo(i: List[ArgInfo]): String = "List(" + i.map(printArgInfo).mkString(",") + ")"

  private def printArgInfo(i: ArgInfo): String = i match {
    case FormulaArg(n, f) => s"""FormulaArg("$n", List(${f.map(quoteString).mkString(",")}))"""
    case GeneratorArg(n) => s"""GeneratorArg("$n")"""
    case ExpressionArg(n, f) => s"""ExpressionArg("$n", List(${f.map(quoteString).mkString(",")}))"""
    case TermArg(n, f) => s"""TermArg("$n", List(${f.map(quoteString).mkString(",")}))"""
    case VariableArg(n, f) => s"""VariableArg("$n", List(${f.map(quoteString).mkString(",")}))"""
    case NumberArg(n, f) => s"""NumberArg("$n", List(${f.map(quoteString).mkString(",")}))"""
    case StringArg(n, f) => s"""StringArg("$n", List(${f.map(quoteString).mkString(",")}))"""
    case SubstitutionArg(n, f) => s"""SubstitutionArg("$n", List(${f.map(quoteString).mkString(",")}))"""
    case PosInExprArg(n, f) => s"""PosInExprArg("$n", List(${f.map(quoteString).mkString(",")}))"""
    case OptionArg(a) => s"""OptionArg(${printArgInfo(a)})"""
    case ListArg(a) => s"""ListArg(${printArgInfo(a)})"""
  }

  private def quoteString(s: String): String = "\"" + s + "\""

}
