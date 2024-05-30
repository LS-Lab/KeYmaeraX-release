/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.hydra.requests.configuration

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.{MathematicaToolProvider, ToolProvider, WolframEngineToolProvider}
import edu.cmu.cs.ls.keymaerax.hydra.responses.configuration.ConfigureMathematicaResponse
import edu.cmu.cs.ls.keymaerax.hydra.{LocalhostOnlyRequest, Response, WriteRequest}
import edu.cmu.cs.ls.keymaerax.tools.install.ToolConfiguration

import scala.collection.immutable.{List, Nil}

class ConfigureMathematicaRequest(toolName: String, linkName: String, jlinkLibFileName: String, jlinkTcpip: String)
    extends LocalhostOnlyRequest with WriteRequest {
  private def isLinkNameCorrect(linkNameFile: java.io.File): Boolean = {
    linkNameFile.getName == "MathKernel" || linkNameFile.getName == "MathKernel.exe"
  }

  private def isJLinkLibFileCorrect(jlinkFile: java.io.File, jlinkLibDir: java.io.File): Boolean = {
    (jlinkFile.getName == "libJLinkNativeLibrary.jnilib" || jlinkFile.getName == "JLinkNativeLibrary.dll" ||
      jlinkFile.getName == "libJLinkNativeLibrary.so") && jlinkLibDir.exists() && jlinkLibDir.isDirectory
  }

  override def resultingResponses(): List[Response] = {
    // check to make sure the indicated files exist and point to the correct files.
    val linkNameFile = new java.io.File(linkName)
    val jlinkLibFile = new java.io.File(jlinkLibFileName)
    val jlinkLibDir: java.io.File = jlinkLibFile.getParentFile
    val linkNameExists = isLinkNameCorrect(linkNameFile) && linkNameFile.exists()
    val jlinkLibFileExists = isJLinkLibFileCorrect(jlinkLibFile, jlinkLibDir) && jlinkLibFile.exists()
    var linkNamePrefix = linkNameFile
    var jlinkLibNamePrefix = jlinkLibFile

    if (!linkNameExists) {
      // look for the largest prefix that does exist
      while (!linkNamePrefix.exists && linkNamePrefix.getParent != null) {
        linkNamePrefix = new java.io.File(linkNamePrefix.getParent)
      }
    }
    if (!jlinkLibFileExists) {
      // look for the largest prefix that does exist
      while (!jlinkLibNamePrefix.exists && jlinkLibNamePrefix.getParent != null) {
        jlinkLibNamePrefix = new java.io.File(jlinkLibNamePrefix.getParent)
      }
    }
    if (!linkNameExists || !jlinkLibFileExists) {
      new ConfigureMathematicaResponse(
        if (linkNamePrefix.exists()) linkNamePrefix.toString else "",
        if (jlinkLibNamePrefix.exists()) jlinkLibNamePrefix.toString else "",
        false,
      ) :: Nil
    } else {
      ToolProvider.shutdown()
      Configuration.set(Configuration.Keys.QE_TOOL, toolName)
      // prefer TCPIP=false if no specific port/machine is configured
      val tcpip = jlinkTcpip match {
        case "true" | "false" =>
          "false" // not user-configurable with this request (but configurable with Advanced options, which then takes precedence)
        case x => x
      }
      val provider = toolName match {
        case "wolframengine" =>
          Configuration.set(Configuration.Keys.WOLFRAMENGINE_TCPIP, tcpip)
          Configuration.set(Configuration.Keys.WOLFRAMENGINE_LINK_NAME, linkNameFile.getAbsolutePath)
          Configuration.set(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR, jlinkLibDir.getAbsolutePath)
          ToolProvider.initFallbackZ3(WolframEngineToolProvider(ToolConfiguration.config(toolName)), "Wolfram Engine")
        case "mathematica" =>
          Configuration.set(Configuration.Keys.MATH_LINK_TCPIP, tcpip)
          Configuration.set(Configuration.Keys.MATHEMATICA_LINK_NAME, linkNameFile.getAbsolutePath)
          Configuration.set(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR, jlinkLibDir.getAbsolutePath)
          ToolProvider.initFallbackZ3(MathematicaToolProvider(ToolConfiguration.config(toolName)), "Mathematica")
      }
      ToolProvider.setProvider(provider)
      new ConfigureMathematicaResponse(linkNameFile.getAbsolutePath, jlinkLibDir.getAbsolutePath, true) :: Nil
    }
  }
}
