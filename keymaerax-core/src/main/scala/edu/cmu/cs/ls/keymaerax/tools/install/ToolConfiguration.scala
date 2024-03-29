package edu.cmu.cs.ls.keymaerax.tools.install

import java.io.File

import edu.cmu.cs.ls.keymaerax.Configuration
import spray.json._
import spray.json.DefaultJsonProtocol._

import scala.collection.immutable.{List, Map}
import scala.io.Source
import scala.util.Try

/**
 * Tool configuration from config file/default configuration.
  *
  * @author Stefan Mitsch
 */
object ToolConfiguration {
  /** Configuration suggestions. */
  case class ConfigSuggestion(version: String, kernelPath: String, kernelName: String, jlinkPath: String, jlinkName: String)

  /** Returns the Mathematica configuration. */
  def mathematicaConfig(preferred: Map[String, String]): Map[String, String] = {
    def tcpip: String = {
      Configuration.getString(Configuration.Keys.MATH_LINK_TCPIP).
        map(s => Try(Integer.parseInt(s)).getOrElse(s).toString).getOrElse("false")
    }

    if (preferred.contains("mathkernel") && preferred.contains("jlink")) {
      Map("mathkernel" -> preferred("mathkernel"), "linkName" -> preferred("mathkernel"),
        "jlink" -> preferred("jlink"), "libDir" -> preferred("jlink"), "tcpip" -> preferred.getOrElse("tcpip", tcpip))
    } else {
      Configuration.getString(Configuration.Keys.MATHEMATICA_LINK_NAME) match {
        case Some(l) => Configuration.getString(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR) match {
          //@todo unify command line name and internal mathematica name (mathkernel vs. linkName, jlink vs libDir)
          case Some(libDir) => Map("mathkernel" -> l, "linkName" -> l, "libDir" -> libDir, "jlink" -> libDir, "tcpip" -> tcpip)
          case None =>
            val libDir = DefaultConfiguration.defaultMathLinkPath._2
            Map("mathkernel" -> l, "linkName" -> l, "libDir" -> libDir, "jlink" -> libDir, "tcpip" -> tcpip)
        }
        case None => DefaultConfiguration.defaultMathematicaConfig

      }
    }
  }

  /** Returns the Wolfram Engine configuration. */
  def wolframEngineConfig(preferred: Map[String, String] = Map.empty): Map[String, String] = {
    def tcpip: String = {
      Configuration.getString(Configuration.Keys.WOLFRAMENGINE_TCPIP).
        map(s => Try(Integer.parseInt(s)).getOrElse(s).toString).getOrElse("true")
    }

    if (preferred.contains("mathkernel") && preferred.contains("jlink")) {
      Map("mathkernel" -> preferred("mathkernel"), "linkName" -> preferred("mathkernel"),
        "jlink" -> preferred("jlink"), "libDir" -> preferred("jlink"), "tcpip" -> preferred.getOrElse("tcpip", tcpip))
    } else {
      Configuration.getString(Configuration.Keys.WOLFRAMENGINE_LINK_NAME) match {
        case Some(l) => Configuration.getString(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR) match {
          //@todo unify command line name and internal mathematica name (mathkernel vs. linkName, jlink vs libDir)
          case Some(libDir) => Map("mathkernel" -> l, "linkName" -> l, "libDir" -> libDir, "jlink" -> libDir, "tcpip" -> tcpip)
          case None =>
            val libDir = DefaultConfiguration.defaultWolframEnginePath._2
            Map("mathkernel" -> l, "linkName" -> l, "libDir" -> libDir, "jlink" -> libDir, "tcpip" -> tcpip)
        }
        case None => DefaultConfiguration.defaultWolframEngineConfig
      }
    }
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
