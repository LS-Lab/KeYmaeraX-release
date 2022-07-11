package edu.cmu.cs.ls.keymaerax

import java.io.PrintWriter
import scala.collection.mutable

/** The hardcoded KeYmaera X configuration for Javascript parsing. */
object JsMapConfiguration extends MapConfiguration(mutable.Map(
  "LAX" -> "true",
  "DEBUG" -> "false",
  "PARSER" -> "DLParser")
) { }
