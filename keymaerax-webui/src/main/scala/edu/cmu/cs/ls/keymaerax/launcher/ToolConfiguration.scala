/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.launcher

import edu.cmu.cs.ls.keymaerax.Configuration

import scala.collection.immutable.Map
import scala.util.Try

/**
 * Tool configuration from config file/default configuration.
 * @author Stefan Mitsch
 */
object ToolConfiguration {
  /** Returns the Mathematica configuration. */
  def mathematicaConfig: Map[String, String] = {
    Configuration.getOption(Configuration.Keys.MATHEMATICA_LINK_NAME) match {
      case Some(l) => Configuration.getOption(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR) match {
        //@todo unify command line name and internal mathematica name (mathkernel vs. linkName)
        case Some(libDir) => Map("mathkernel" -> l, "linkName" -> l, "jlink" -> libDir)
        case None => Map("mathkernel" -> l, "linkName" -> l)
      }
      case None => DefaultConfiguration.defaultMathematicaConfig

    }
  }

  /** Returns the Wolfram Engine configuration. */
  def wolframEngineConfig: Map[String, String] = {
    def tcpip: String = {
      Configuration.getOption(Configuration.Keys.MATH_LINK_TCPIP).
        map(s => Try(Integer.parseInt(s)).getOrElse("true").toString).getOrElse("true")
    }

    Configuration.getOption(Configuration.Keys.MATHEMATICA_LINK_NAME) match {
      case Some(l) => Configuration.getOption(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR) match {
        //@todo unify command line name and internal mathematica name (mathkernel vs. linkName)
        case Some(libDir) => Map("mathkernel" -> l, "linkName" -> l, "jlink" -> libDir, "tcpip" -> tcpip)
        case None => Map("mathkernel" -> l, "linkName" -> l, "tcpip" -> tcpip)
      }
      case None => DefaultConfiguration.defaultMathematicaConfig

    }
  }

  /** Returns the Wolfram Engine configuration. */
  def wolframScriptConfig: Map[String, String] = Map.empty

  /** Returns the Z3 configuration. */
  def z3Config: Map[String, String] = Map.empty

  /** Returns the tool configuration for the name `tool`. */
  def config(tool: String): Map[String, String] = tool.toLowerCase() match {
    case "mathematica" => Map("tool" -> "mathematica") ++ ToolConfiguration.mathematicaConfig
    case "wolframengine" => Map("tool" -> "wolframengine") ++ ToolConfiguration.wolframEngineConfig
    case "wolframscript" => Map("tool" -> "wolframscript") ++ ToolConfiguration.wolframScriptConfig
    case "z3" => Map("tool" -> "z3") ++ ToolConfiguration.z3Config
    case t => throw new Exception("Unknown tool '" + t + "'")
  }
}
