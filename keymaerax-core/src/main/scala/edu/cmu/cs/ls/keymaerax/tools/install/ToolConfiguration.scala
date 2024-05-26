/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools.install

import edu.cmu.cs.ls.keymaerax.Configuration

import scala.util.Try

/**
 * Tool configuration from config file/default configuration.
 *
 * @author
 *   Stefan Mitsch
 */
object ToolConfiguration {

  /** Returns the Mathematica configuration. */
  def mathematicaConfig(preferred: Map[String, String]): Map[String, String] = {
    def tcpip: String = {
      Configuration
        .getString(Configuration.Keys.MATH_LINK_TCPIP)
        .map(s => Try(Integer.parseInt(s)).getOrElse(s).toString)
        .getOrElse("false")
    }

    if (preferred.contains("mathkernel") && preferred.contains("jlink")) return Map(
      "mathkernel" -> preferred("mathkernel"),
      "linkName" -> preferred("mathkernel"),
      "jlink" -> preferred("jlink"),
      "libDir" -> preferred("jlink"),
      "tcpip" -> preferred.getOrElse("tcpip", tcpip),
    )

    val defaultConfig = DefaultConfiguration.defaultMathematicaConfig

    val linkName = Configuration.getString(Configuration.Keys.MATHEMATICA_LINK_NAME).getOrElse(return defaultConfig)

    val libDir = Configuration
      .getString(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR)
      .getOrElse(defaultConfig("libDir"))

    // @todo unify command line name and internal mathematica name (mathkernel vs. linkName, jlink vs libDir)
    Map("mathkernel" -> linkName, "linkName" -> linkName, "libDir" -> libDir, "jlink" -> libDir, "tcpip" -> tcpip)
  }

  /** Returns the Wolfram Engine configuration. */
  def wolframEngineConfig(preferred: Map[String, String] = Map.empty): Map[String, String] = {
    def tcpip: String = {
      Configuration
        .getString(Configuration.Keys.WOLFRAMENGINE_TCPIP)
        .map(s => Try(Integer.parseInt(s)).getOrElse(s).toString)
        .getOrElse("true")
    }

    if (preferred.contains("mathkernel") && preferred.contains("jlink")) return Map(
      "mathkernel" -> preferred("mathkernel"),
      "linkName" -> preferred("mathkernel"),
      "jlink" -> preferred("jlink"),
      "libDir" -> preferred("jlink"),
      "tcpip" -> preferred.getOrElse("tcpip", tcpip),
    )

    val defaultConfig = DefaultConfiguration.defaultWolframEngineConfig

    val linkName = Configuration.getString(Configuration.Keys.WOLFRAMENGINE_LINK_NAME).getOrElse(return defaultConfig)

    val libDir = Configuration
      .getString(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR)
      .getOrElse(defaultConfig("libDir"))

    // @todo unify command line name and internal mathematica name (mathkernel vs. linkName, jlink vs libDir)
    Map("mathkernel" -> linkName, "linkName" -> linkName, "libDir" -> libDir, "jlink" -> libDir, "tcpip" -> tcpip)
  }

  /** Returns the Wolfram Engine configuration. */
  def wolframScriptConfig(preferred: Map[String, String] = Map.empty): Map[String, String] = preferred

  /** Returns the Z3 configuration. */
  def z3Config(preferred: Map[String, String] = Map.empty): Map[String, String] = preferred

  /** Returns the tool configuration for the name `tool`. */
  def config(tool: String, preferred: Map[String, String] = Map.empty): Map[String, String] = tool.toLowerCase() match {
    case "mathematica" => Map("tool" -> "mathematica") ++ ToolConfiguration.mathematicaConfig(preferred)
    case "wolframengine" => Map("tool" -> "wolframengine") ++ ToolConfiguration.wolframEngineConfig(preferred)
    case "wolframscript" => Map("tool" -> "wolframscript") ++ ToolConfiguration.wolframScriptConfig(preferred)
    case "z3" => Map("tool" -> "z3") ++ ToolConfiguration.z3Config(preferred)
    case t => throw new Exception("Unknown tool '" + t + "'")
  }
}
