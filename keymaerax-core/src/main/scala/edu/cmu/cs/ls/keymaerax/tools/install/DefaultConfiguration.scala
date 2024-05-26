/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools.install

import edu.cmu.cs.ls.keymaerax.tools.ToolPathFinder

/**
 * Created by smitsch on 7/14/15.
 *
 * @author
 *   Stefan Mitsch
 * @author
 *   Ran Ji
 */
object DefaultConfiguration {
  def defaultMathematicaConfig: Map[String, String] = {
    val paths = ToolPathFinder
      .findMathematicaInstallDir()
      .flatMap(ToolPathFinder.findMathematicaPaths)
      .getOrElse(return Map.empty)

    Map(
      "mathkernel" -> paths.mathKernel.toString,
      "linkName" -> paths.mathKernel.toString,
      "jlink" -> paths.jlinkLib.getParent.toString,
      "libDir" -> paths.jlinkLib.getParent.toString,
      "tcpip" -> "false",
    )
  }

  def defaultWolframEngineConfig: Map[String, String] = {
    val paths = ToolPathFinder
      .findMathematicaInstallDir()
      .flatMap(ToolPathFinder.findMathematicaPaths)
      .getOrElse(return Map.empty)

    Map(
      "mathkernel" -> paths.mathKernel.toString,
      "linkName" -> paths.mathKernel.toString,
      "jlink" -> paths.jlinkLib.getParent.toString,
      "libDir" -> paths.jlinkLib.getParent.toString,
      "tcpip" -> "true",
    )
  }
}
