/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools.install

import java.util.Locale

import scala.collection.immutable.Map

/**
 * Created by smitsch on 7/14/15.
 *
 * @author
 *   Stefan Mitsch
 * @author
 *   Ran Ji
 */
object DefaultConfiguration {

  /** The Mathematica config as set from the command line (default config if not set) */
  var currentMathematicaConfig: Map[String, String] = defaultMathematicaConfig

  def defaultMathLinkName: (String, String) = {
    var kernelName = ""
    var jlinkFileName = ""
    val osName = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)
    if (osName.contains("mac")) {
      kernelName = "MathKernel"
      jlinkFileName = "libJLinkNativeLibrary.jnilib"
    } else if (osName.contains("windows")) {
      kernelName = "MathKernel.exe"
      jlinkFileName = "JLinkNativeLibrary.dll"
    } else if (osName.contains("linux")) {
      kernelName = "MathKernel"
      jlinkFileName = "libJLinkNativeLibrary.so"
    }
    (kernelName, jlinkFileName)
  }

  def defaultMathematicaConfig: Map[String, String] = {
    if (defaultMathLinkPath._1 != "" && defaultMathLinkPath._2 != "") Map(
      "mathkernel" -> defaultMathLinkPath._1,
      "linkName" -> defaultMathLinkPath._1,
      "jlink" -> defaultMathLinkPath._2,
      "libDir" -> defaultMathLinkPath._2,
      "tcpip" -> "false",
    )
    else Map.empty
  }

  def defaultWolframEngineConfig: Map[String, String] = {
    if (defaultWolframEnginePath._1 != "" && defaultWolframEnginePath._2 != "") Map(
      "mathkernel" -> defaultWolframEnginePath._1,
      "linkName" -> defaultWolframEnginePath._1,
      "jlink" -> defaultWolframEnginePath._2,
      "libDir" -> defaultWolframEnginePath._2,
      "tcpip" -> "true",
    )
    else Map.empty
  }

  def defaultMathLinkPath: (String, String) = {
    val allSuggestions = ToolConfiguration.mathematicaSuggestion()
    val suggestion = allSuggestions.find(s =>
      new java.io.File(s.kernelPath + s.kernelName).exists && new java.io.File(s.jlinkPath + s.jlinkName).exists
    ) match {
      case Some(s) => s
      case None => allSuggestions.head // use the first configuration as suggestion when nothing else matches
    }
    (suggestion.kernelPath + suggestion.kernelName, suggestion.jlinkPath)
  }

  def defaultWolframEnginePath: (String, String) = {
    val allSuggestions = ToolConfiguration.wolframEngineSuggestion()
    val suggestion = allSuggestions.find(s =>
      new java.io.File(s.kernelPath + s.kernelName).exists && new java.io.File(s.jlinkPath + s.jlinkName).exists
    ) match {
      case Some(s) => s
      case None => allSuggestions.head // use the first configuration as suggestion when nothing else matches
    }
    (suggestion.kernelPath + suggestion.kernelName, suggestion.jlinkPath)
  }

  def exemplaryMathLinkPath: (String, String) = {
    val s = ToolConfiguration.mathematicaSuggestion().head
    (s.kernelPath, s.jlinkPath)
  }
}
