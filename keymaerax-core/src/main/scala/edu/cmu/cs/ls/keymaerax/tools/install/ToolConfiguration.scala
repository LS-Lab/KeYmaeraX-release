/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools.install

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.tools.{ToolName, ToolPathFinder}

import scala.util.Try

case class ToolConfiguration(
    tool: Option[ToolName.Value] = None,
    mathKernel: Option[String] = None,
    jlinkLibDir: Option[String] = None,
    tcpip: Option[String] = None,
    z3Path: Option[String] = None,
)

/**
 * Tool configuration from config file/default configuration.
 *
 * @author
 *   Stefan Mitsch
 */
object ToolConfiguration {
  def defaultMathematicaConfig: ToolConfiguration = {
    val paths = ToolPathFinder
      .findMathematicaInstallDir()
      .flatMap(ToolPathFinder.findMathematicaPaths)
      .getOrElse(return ToolConfiguration())

    ToolConfiguration(
      mathKernel = Some(paths.mathKernel.toString),
      jlinkLibDir = Some(paths.jlinkLib.getParent.toString),
      tcpip = Some("false"),
    )
  }

  /** Returns the Mathematica configuration. */
  def mathematicaConfig(preferred: ToolConfiguration = ToolConfiguration()): ToolConfiguration = {
    def tcpip: String = Configuration
      .getString(Configuration.Keys.MATH_LINK_TCPIP)
      .map(s => Try(Integer.parseInt(s)).getOrElse(s).toString)
      .getOrElse("false")

    if (preferred.mathKernel.isDefined && preferred.jlinkLibDir.isDefined)
      return preferred.copy(tcpip = preferred.tcpip.orElse(Some(tcpip)))

    val defaultConfig = defaultMathematicaConfig

    val linkName = Configuration.getString(Configuration.Keys.MATHEMATICA_LINK_NAME).getOrElse(return defaultConfig)

    val libDir = Configuration
      .getString(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR)
      .getOrElse(defaultConfig.jlinkLibDir.get)

    ToolConfiguration(mathKernel = Some(linkName), jlinkLibDir = Some(libDir), tcpip = Some(tcpip))
  }

  def defaultWolframEngineConfig: ToolConfiguration = {
    val paths = ToolPathFinder
      .findMathematicaInstallDir()
      .flatMap(ToolPathFinder.findMathematicaPaths)
      .getOrElse(return ToolConfiguration())

    ToolConfiguration(
      mathKernel = Some(paths.mathKernel.toString),
      jlinkLibDir = Some(paths.jlinkLib.getParent.toString),
      tcpip = Some("true"),
    )
  }

  /** Returns the Wolfram Engine configuration. */
  def wolframEngineConfig(preferred: ToolConfiguration = ToolConfiguration()): ToolConfiguration = {
    def tcpip: String = Configuration
      .getString(Configuration.Keys.WOLFRAMENGINE_TCPIP)
      .map(s => Try(Integer.parseInt(s)).getOrElse(s).toString)
      .getOrElse("true")

    if (preferred.mathKernel.isDefined && preferred.jlinkLibDir.isDefined)
      return preferred.copy(tcpip = preferred.tcpip.orElse(Some(tcpip)))

    val defaultConfig = defaultWolframEngineConfig

    val linkName = Configuration.getString(Configuration.Keys.WOLFRAMENGINE_LINK_NAME).getOrElse(return defaultConfig)

    val libDir = Configuration
      .getString(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR)
      .getOrElse(defaultConfig.jlinkLibDir.get)

    ToolConfiguration(mathKernel = Some(linkName), jlinkLibDir = Some(libDir), tcpip = Some(tcpip))
  }

  /** Returns the Wolfram Engine configuration. */
  def wolframScriptConfig(preferred: ToolConfiguration = ToolConfiguration()): ToolConfiguration = preferred

  /** Returns the Z3 configuration. */
  def z3Config(preferred: ToolConfiguration = ToolConfiguration()): ToolConfiguration = preferred

  /** Returns the tool configuration for the name `tool`. */
  def config(tool: ToolName.Value, preferred: ToolConfiguration = ToolConfiguration()): ToolConfiguration =
    (tool match {
      case ToolName.Mathematica => mathematicaConfig(preferred)
      case ToolName.WolframEngine => wolframEngineConfig(preferred)
      case ToolName.WolframScript => wolframScriptConfig(preferred)
      case ToolName.Z3 => z3Config(preferred)
    }).copy(tool = Some(tool))
}
