/**
  * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.launcher

import java.io.File

import edu.cmu.cs.ls.keymaerax.Configuration
import spray.json._
import spray.json.DefaultJsonProtocol._

import scala.collection.immutable.{List, Map}
import scala.io.Source
import scala.util.Try

/**
 * Tool configuration from config file/default configuration.
 * @author Stefan Mitsch
 */
object ToolConfiguration {
  /** Configuration suggestions. */
  case class ConfigSuggestion(version: String, kernelPath: String, kernelName: String, jlinkPath: String, jlinkName: String)

  /** Returns the Mathematica configuration. */
  def mathematicaConfig: Map[String, String] = {
    def tcpip: String = {
      Configuration.getOption(Configuration.Keys.MATH_LINK_TCPIP).
        map(s => Try(Integer.parseInt(s)).getOrElse(s).toString).getOrElse("false")
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
  def wolframEngineConfig: Map[String, String] = {
    def tcpip: String = {
      Configuration.getOption(Configuration.Keys.MATH_LINK_TCPIP).
        map(s => Try(Integer.parseInt(s)).getOrElse(s).toString).getOrElse("true")
    }

    Configuration.getOption(Configuration.Keys.MATHEMATICA_LINK_NAME) match {
      case Some(l) => Configuration.getOption(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR) match {
        //@todo unify command line name and internal mathematica name (mathkernel vs. linkName)
        case Some(libDir) => Map("mathkernel" -> l, "linkName" -> l, "jlink" -> libDir, "tcpip" -> tcpip)
        case None => Map("mathkernel" -> l, "linkName" -> l, "tcpip" -> tcpip)
      }
      case None => DefaultConfiguration.defaultWolframEngineConfig

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

  /** Returns suggestions for Mathematica configuration. */
  def mathematicaSuggestion(): List[ConfigSuggestion] = parseSuggestions("/config/potentialMathematicaPaths.json")
  /** Returns suggestions for Wolfram Engine configuration */
  def wolframEngineSuggestion(): List[ConfigSuggestion] = parseSuggestions("/config/potentialWolframEnginePaths.json")

  /** Returns readable names for Java OS names. */
  private def osKeyOf(osName: String): String = {
    if (osName.contains("win")) "Windows"
    else if (osName.contains("mac")) "MacOS"
    else if (osName.contains("nix") || osName.contains("nux") || osName.contains("aix")) "Unix"
    else "Unknown"
  }

  /** Parses a suggestions JSON file. */
  private def parseSuggestions(suggestionsFile: String): List[ConfigSuggestion] = {
    val reader = this.getClass.getResourceAsStream(suggestionsFile)
    val contents: String = Source.fromInputStream(reader).mkString
    val source: JsArray = contents.parseJson.asInstanceOf[JsArray]

    // TODO provide classes and spray JSON protocol to convert
    val os = System.getProperty("os.name")
    val osKey = osKeyOf(os.toLowerCase)
    val jvmBits = System.getProperty("sun.arch.data.model")
    val osPathGuesses = source.elements.find(osCfg => osCfg.asJsObject.getFields("os").head.convertTo[String] == osKey) match {
      case Some(opg) => opg.asJsObject.getFields("paths").head.convertTo[List[JsObject]]
      case None => throw new IllegalStateException("No default configuration for Unknown OS")
    }

    osPathGuesses.map(osPath =>
      (osPath.getFields("version").head.convertTo[String],
        osPath.getFields("kernelPath").head.convertTo[List[String]],
        osPath.getFields("kernelName").head.convertTo[String],
        osPath.getFields("jlinkPath").head.convertTo[List[String]].map(p => p +
          (if (jvmBits == "64") "-" + jvmBits else "") + File.separator),
        osPath.getFields("jlinkName").head.convertTo[String])).flatMap({
      case (p1, p2, p3, p4, p5) => p2.zipWithIndex.map({ case (p, i) => ConfigSuggestion(p1, p, p3, p4(i), p5) })
    })
  }
}
