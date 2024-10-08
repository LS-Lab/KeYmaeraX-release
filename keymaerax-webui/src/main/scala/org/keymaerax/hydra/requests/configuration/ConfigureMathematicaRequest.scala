/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.hydra.requests.configuration

import org.keymaerax.Configuration
import org.keymaerax.btactics.{MathematicaToolProvider, ToolProvider, WolframEngineToolProvider}
import org.keymaerax.hydra.responses.configuration.ConfigureMathematicaResponse
import org.keymaerax.hydra.{LocalhostOnlyRequest, Response, WriteRequest}
import org.keymaerax.tools.ToolName
import org.keymaerax.tools.install.ToolConfiguration

class ConfigureMathematicaRequest(tool: ToolName.Value, linkName: String, jlinkLibFileName: String, jlinkTcpip: String)
    extends LocalhostOnlyRequest with WriteRequest {

  private def isLinkNameCorrect(linkNameFile: java.io.File): Boolean = {
    linkNameFile.getName == "MathKernel" || linkNameFile.getName == "MathKernel.exe"
  }

  private def isJLinkLibFileCorrect(jlinkFile: java.io.File, jlinkLibDir: java.io.File): Boolean = {
    (jlinkFile.getName == "libJLinkNativeLibrary.jnilib" || jlinkFile.getName == "JLinkNativeLibrary.dll" ||
      jlinkFile.getName == "libJLinkNativeLibrary.so") && jlinkLibDir.exists() && jlinkLibDir.isDirectory
  }

  override def resultingResponse(): Response = {
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
      )
    } else {
      ToolProvider.shutdown()
      Configuration.set(Configuration.Keys.QE_TOOL, tool.toString)
      // prefer TCPIP=false if no specific port/machine is configured
      val tcpip = jlinkTcpip match {
        case "true" | "false" =>
          "false" // not user-configurable with this request (but configurable with Advanced options, which then takes precedence)
        case x => x
      }
      val provider = tool match {
        case ToolName.WolframEngine =>
          Configuration.set(Configuration.Keys.WOLFRAMENGINE_TCPIP, tcpip)
          Configuration.set(Configuration.Keys.WOLFRAMENGINE_LINK_NAME, linkNameFile.getAbsolutePath)
          Configuration.set(Configuration.Keys.WOLFRAMENGINE_JLINK_LIB_DIR, jlinkLibDir.getAbsolutePath)
          ToolProvider.initFallbackZ3(WolframEngineToolProvider(ToolConfiguration.config(tool)), "Wolfram Engine")
        case ToolName.Mathematica =>
          Configuration.set(Configuration.Keys.MATH_LINK_TCPIP, tcpip)
          Configuration.set(Configuration.Keys.MATHEMATICA_LINK_NAME, linkNameFile.getAbsolutePath)
          Configuration.set(Configuration.Keys.MATHEMATICA_JLINK_LIB_DIR, jlinkLibDir.getAbsolutePath)
          ToolProvider.initFallbackZ3(MathematicaToolProvider(ToolConfiguration.config(tool)), "Mathematica")
      }
      ToolProvider.setProvider(provider)
      new ConfigureMathematicaResponse(linkNameFile.getAbsolutePath, jlinkLibDir.getAbsolutePath, true)
    }
  }
}
