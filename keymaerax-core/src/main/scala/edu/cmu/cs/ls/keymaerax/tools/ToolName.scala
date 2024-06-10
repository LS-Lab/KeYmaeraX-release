/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools

import java.util.Locale

// TODO Turn into Scala 3 enum
object ToolName extends Enumeration {
  val Mathematica: Value = Value
  val WolframEngine: Value = Value
  val WolframScript: Value = Value
  val Z3: Value = Value

  def parse(s: String): Value = s.toLowerCase(Locale.ROOT) match {
    case "mathematica" => ToolName.Mathematica
    case "wolframengine" => ToolName.WolframEngine
    case "wolframscript" => ToolName.WolframScript
    case "z3" => ToolName.Z3
    case _ => throw new Exception(s"Unknown tool: '$s'")
  }
}
