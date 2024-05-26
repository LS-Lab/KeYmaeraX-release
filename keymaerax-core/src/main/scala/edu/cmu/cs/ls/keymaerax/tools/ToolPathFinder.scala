/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.info.{ArchType, Os, OsType}

import java.nio.file.{Path, Paths}
import scala.sys.process.Process
import scala.util.Try

object ToolPathFinder {
  case class MathematicaPaths(mathKernel: Path, jlinkLib: Path)

  @deprecated("use findMathematicaPaths instead")
  def jlinkLibFileName: String = findMathematicaPaths(Paths.get(".")).map(_.jlinkLib.getFileName.toString).getOrElse("")

  /** Find the Mathematica installation directory by asking different programs on the `PATH`. */
  def findMathematicaInstallDir(): Option[Path] = {
    def pathFromCommand(command: String*): Option[Path] = Try(Paths.get(Process(command).!!.stripLineEnd)).toOption

    // On Windows, Mathematica/WolframEngine only adds wolframscript.exe to the PATH.
    // On other platforms, wolframscript may also be available, but not always.
    // For example, Mathematica on NixOS does not provide wolframscript.
    // https://reference.wolfram.com/language/ref/$InstallationDirectory.html
    // https://reference.wolfram.com/language/ref/program/wolframscript.html
    def pathFromWolframscript = pathFromCommand("wolframscript", "-code", "$InstallationDirectory")

    // On non-Windows platforms, Mathematica/WolframEngine may add more binaries to the PATH:
    // wolfram, WolframKernel, math, and MathKernel.
    // Of those, math/MathKernel are equivalent to wolfram/WolframKernel and only provided for backwards compatibility.
    // https://mathematica.stackexchange.com/a/84038
    //
    // The wolfram binary is meant for command-line use while the WolframKernel binary may spawn a GUI.
    // Because of this, we use the wolfram binary to retrieve the installation directory if wolframscript failed.
    // https://reference.wolfram.com/language/ref/$InstallationDirectory.html
    // https://reference.wolfram.com/language/ref/program/wolfram.html
    // https://mathematica.stackexchange.com/q/648
    def pathFromWolfram =
      pathFromCommand("wolfram", "-noprompt", "-run", "WriteString[$Output,$InstallationDirectory];Exit[]")

    // If necessary, we could try the default installation directory paths as additional fallbacks.
    // Hopefully the above commands are sufficient though.
    pathFromWolframscript.orElse(pathFromWolfram)
  }

  /**
   * Find paths to specific files inside a Mathematica installation. Use [[findMathematicaInstallDir]] to find the
   * installation itself.
   */
  def findMathematicaPaths(installDir: Path): Option[MathematicaPaths] = {
    val mathKernelPath = Os.Type match {
      case OsType.Windows => Paths.get("MathKernel.exe")
      case OsType.Linux => Paths.get("Executables", "MathKernel")
      case OsType.MacOs => Paths.get("MacOS", "MathKernel")
      case OsType.Unknown => return None
    }

    val jlinkDirName = {
      val base = Os.Type match {
        case OsType.Windows => "Windows"
        case OsType.Linux => "Linux"
        case OsType.MacOs => "MacOSX"
        case OsType.Unknown => return None
      }
      val ext = Os.Arch match {
        case ArchType.Amd64 => "x86-64"
        case ArchType.Aarch64 => "ARM64"
        case ArchType.Unknown => return None
      }
      s"$base-$ext"
    }

    val jlinkLibName = Os.Type match {
      case OsType.Windows => "JLinkNativeLibrary.dll"
      case OsType.Linux => "libJLinkNativeLibrary.so"
      case OsType.MacOs => "libJLinkNativeLibrary.jnilib"
      case OsType.Unknown => return None
    }

    val jlinkLibPath = Paths
      .get("SystemFiles", "Links", "JLink", "SystemFiles", "Libraries", jlinkDirName, jlinkLibName)

    Some(MathematicaPaths(mathKernel = installDir.resolve(mathKernelPath), jlinkLib = installDir.resolve(jlinkLibPath)))
  }
}
