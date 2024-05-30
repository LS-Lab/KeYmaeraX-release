/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools.install

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.tools.ToolPathFinder

import scala.util.Try

case class ToolConfiguration(
    tool: Option[String] = None,
    mathkernel: Option[String] = None,
    linkName: Option[String] = None,
    jlink: Option[String] = None,
    libDir: Option[String] = None,
    tcpip: Option[String] = None,
    z3Path: Option[String] = None,
) {
  def toMap: Map[String, String] = Seq(
    this.tool.map("tool" -> _),
    this.mathkernel.map("mathkernel" -> _),
    this.linkName.map("linkName" -> _),
    this.jlink.map("jlink" -> _),
    this.libDir.map("libDir" -> _),
    this.tcpip.map("tcpip" -> _),
    this.z3Path.map("z3Path" -> _),
  ).flatten.toMap
}

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
      mathkernel = Some(paths.mathKernel.toString),
      linkName = Some(paths.mathKernel.toString),
      jlink = Some(paths.jlinkLib.getParent.toString),
      libDir = Some(paths.jlinkLib.getParent.toString),
      tcpip = Some("false"),
    )
  }

  /** Returns the Mathematica configuration. */
  def mathematicaConfig(preferred: ToolConfiguration = ToolConfiguration()): ToolConfiguration = {
    def tcpip: String = {
      Configuration
        .getString(Configuration.Keys.MATH_LINK_TCPIP)
        .map(s => Try(Integer.parseInt(s)).getOrElse(s).toString)
        .getOrElse("false")
    }

    if (preferred.mathkernel.isDefined && preferred.jlink.isDefined) return ToolConfiguration(
      mathkernel = Some(preferred.mathkernel.get),
      linkName = Some(preferred.mathkernel.get),
      jlink = Some(preferred.jlink.get),
      libDir = Some(preferred.jlink.get),
      tcpip = Some(preferred.tcpip.getOrElse(tcpip)),
    )

    val defaultConfig = defaultMathematicaConfig

    val linkName = Configuration.getString(Configuration.Keys.MATHEMATICA_LINK_NAME).getOrElse(return defaultConfig)

    val libDir = Configuration
      .getString(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR)
      .getOrElse(defaultConfig.libDir.get)

    // @todo unify command line name and internal mathematica name (mathkernel vs. linkName, jlink vs libDir)
    ToolConfiguration(
      mathkernel = Some(linkName),
      linkName = Some(linkName),
      libDir = Some(libDir),
      jlink = Some(libDir),
      tcpip = Some(tcpip),
    )
  }

  def defaultWolframEngineConfig: ToolConfiguration = {
    val paths = ToolPathFinder
      .findMathematicaInstallDir()
      .flatMap(ToolPathFinder.findMathematicaPaths)
      .getOrElse(return ToolConfiguration())

    ToolConfiguration(
      mathkernel = Some(paths.mathKernel.toString),
      linkName = Some(paths.mathKernel.toString),
      jlink = Some(paths.jlinkLib.getParent.toString),
      libDir = Some(paths.jlinkLib.getParent.toString),
      tcpip = Some("true"),
    )
  }

  /** Returns the Wolfram Engine configuration. */
  def wolframEngineConfig(preferred: ToolConfiguration = ToolConfiguration()): ToolConfiguration = {
    def tcpip: String = {
      Configuration
        .getString(Configuration.Keys.WOLFRAMENGINE_TCPIP)
        .map(s => Try(Integer.parseInt(s)).getOrElse(s).toString)
        .getOrElse("true")
    }

    if (preferred.mathkernel.isDefined && preferred.jlink.isDefined) return ToolConfiguration(
      mathkernel = Some(preferred.mathkernel.get),
      linkName = Some(preferred.mathkernel.get),
      jlink = Some(preferred.jlink.get),
      libDir = Some(preferred.jlink.get),
      tcpip = Some(preferred.tcpip.getOrElse(tcpip)),
    )

    val defaultConfig = defaultWolframEngineConfig

    val linkName = Configuration.getString(Configuration.Keys.WOLFRAMENGINE_LINK_NAME).getOrElse(return defaultConfig)

    val libDir = Configuration
      .getString(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR)
      .getOrElse(defaultConfig.libDir.get)

    // @todo unify command line name and internal mathematica name (mathkernel vs. linkName, jlink vs libDir)
    ToolConfiguration(
      mathkernel = Some(linkName),
      linkName = Some(linkName),
      libDir = Some(libDir),
      jlink = Some(libDir),
      tcpip = Some(tcpip),
    )
  }

  /** Returns the Wolfram Engine configuration. */
  def wolframScriptConfig(preferred: ToolConfiguration = ToolConfiguration()): ToolConfiguration = preferred

  /** Returns the Z3 configuration. */
  def z3Config(preferred: ToolConfiguration = ToolConfiguration()): ToolConfiguration = preferred

  /** Returns the tool configuration for the name `tool`. */
  def config(tool: String, preferred: ToolConfiguration = ToolConfiguration()): ToolConfiguration =
    tool.toLowerCase() match {
      case "mathematica" => mathematicaConfig(preferred).copy(tool = Some("mathematica"))
      case "wolframengine" => wolframEngineConfig(preferred).copy(tool = Some("wolframengine"))
      case "wolframscript" => wolframScriptConfig(preferred).copy(tool = Some("wolframscript"))
      case "z3" => z3Config(preferred).copy(tool = Some("z3"))
      case t => throw new Exception("Unknown tool '" + t + "'")
    }
}
