/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.tools

import org.keymaerax.info.{ArchType, Os, OsType}

import java.nio.file.{Files, Path, Paths}
import scala.sys.process.Process
import scala.util.Try

object ToolPathFinder {
  case class MathematicaPaths(mathKernel: Path, jlinkLib: Path)

  @deprecated("use findMathematicaPaths instead")
  def jlinkLibFileName: String = findMathematicaPaths(Paths.get(".")).map(_.jlinkLib.getFileName.toString).getOrElse("")

  private def parseVersion(s: String): Option[(Int, Int)] = {
    val matched = """^(\d+)\.(\d+)$""".r.findFirstMatchIn(s).getOrElse(return None)
    val major = Try(Integer.parseInt(matched.group(1))).getOrElse(return None)
    val minor = Try(Integer.parseInt(matched.group(2))).getOrElse(return None)
    Some((major, minor))
  }

  private def sortPathsByTrailingVersion(paths: Seq[Path]): Seq[Path] = paths
    .sorted
    .sortBy(p => parseVersion(p.getFileName.toString))
    .reverse

  /**
   * Search for any directories that match the default Mathematica installation directory pattern. This function does
   * not check that the directories contain working installations. If multiple directories match the pattern (i.e. the
   * user has multiple different versions of Mathematica installed), they are ordered from newest to oldest.
   *
   * [[https://reference.wolfram.com/language/tutorial/WolframSystemFileOrganization.html]]
   */
  private def defaultMathematicaInstallDirCandidates: Seq[Path] = {
    import scala.jdk.StreamConverters._
    Try(Os.Type match {
      case OsType.Windows =>
        val base = Paths.get("C:\\Program Files\\Wolfram Research\\Mathematica")
        sortPathsByTrailingVersion(Files.list(base).toScala(Seq))
      case OsType.Linux =>
        val base = Paths.get("/usr/local/Wolfram/Mathematica")
        sortPathsByTrailingVersion(Files.list(base).toScala(Seq))
      case OsType.MacOs => Paths.get("/Applications/Mathematica.app/Contents") :: Nil
      case OsType.Unknown => Nil
    }).getOrElse(Nil)
  }

  /**
   * Search for any directories that match the default Wolfram Engine installation directory pattern. This function does
   * not check that the directories contain working installations. If multiple directories match the pattern (i.e. the
   * user has multiple different versions of Wolfram Engine installed), they are ordered from newest to oldest.
   *
   * See also [[defaultMathematicaInstallDirCandidates]].
   */
  private def defaultWolframEngineInstallDirCandidates: Seq[Path] = {
    import scala.jdk.StreamConverters._
    Try(Os.Type match {
      case OsType.Windows =>
        val base = Paths.get("C:\\Program Files\\Wolfram Research\\Wolfram Engine")
        sortPathsByTrailingVersion(Files.list(base).toScala(Seq))
      case OsType.Linux =>
        val base = Paths.get("/usr/local/Wolfram/WolframEngine")
        sortPathsByTrailingVersion(Files.list(base).toScala(Seq))
      case OsType.MacOs => Paths.get("/Applications/Wolfram Engine.app/Contents") :: Nil
      case OsType.Unknown => Nil
    }).getOrElse(Nil)
  }

  private def wolframscriptPath: Option[Path] = Os.Type match {
    case OsType.Windows => Some(Paths.get("wolframscript.exe"))
    case OsType.Linux => Some(Paths.get("Executables", "wolframscript"))
    case OsType.MacOs => Some(Paths.get("MacOS", "wolframscript"))
    case OsType.Unknown => None
  }

  private def wolframPath: Option[Path] = Os.Type match {
    case OsType.Windows => Some(Paths.get("wolfram.exe"))
    case OsType.Linux => Some(Paths.get("Executables", "wolfram"))
    case OsType.MacOs => Some(Paths.get("MacOS", "wolfram"))
    case OsType.Unknown => None
  }

  private def mathKernelPath: Option[Path] = Os.Type match {
    case OsType.Windows => Some(Paths.get("MathKernel.exe"))
    case OsType.Linux => Some(Paths.get("Executables", "MathKernel"))
    case OsType.MacOs => Some(Paths.get("MacOS", "MathKernel"))
    case OsType.Unknown => None
  }

  private def jlinkLibPath: Option[Path] = {
    val osName = Os.Type match {
      case OsType.Windows => "Windows"
      case OsType.Linux => "Linux"
      case OsType.MacOs => "MacOSX"
      case OsType.Unknown => return None
    }

    val osArch = Os.Arch match {
      case ArchType.Amd64 => "x86-64"
      case ArchType.Aarch64 => "ARM64"
      case ArchType.Unknown => return None
    }

    val jlinkDirName = s"$osName-$osArch"

    val jlinkLibName = Os.Type match {
      case OsType.Windows => "JLinkNativeLibrary.dll"
      case OsType.Linux => "libJLinkNativeLibrary.so"
      case OsType.MacOs => "libJLinkNativeLibrary.jnilib"
      case OsType.Unknown => return None
    }

    Some(Paths.get("SystemFiles", "Links", "JLink", "SystemFiles", "Libraries", jlinkDirName, jlinkLibName))
  }

  /**
   * Execute a command that will print only a path (and an optional trailing newline) on stdout. Returns the path if no
   * errors occur during execution.
   */
  private def installDirFromCommand(command: String*): Option[Path] = Try(Paths.get(Process(command).!!.stripLineEnd))
    .toOption

  /**
   * Obtain the installation directory from a `wolframscript` binary.
   *
   *   - [[https://reference.wolfram.com/language/ref/$InstallationDirectory.html]]
   *   - [[https://reference.wolfram.com/language/ref/program/wolframscript.html]]
   */
  private def installDirFromWolframscript(binary: String = "wolframscript"): Option[Path] =
    installDirFromCommand(binary, "-code", "$InstallationDirectory")

  /**
   * Obtain the installation directory from a `wolfram` kernel.
   *
   *   - [[https://reference.wolfram.com/language/ref/$InstallationDirectory.html]]
   *   - [[https://reference.wolfram.com/language/ref/program/wolfram.html]]
   *   - [[https://mathematica.stackexchange.com/q/648]]
   */
  private def installDirFromWolfram(binary: String = "wolfram"): Option[Path] =
    installDirFromCommand(binary, "-noprompt", "-run", "WriteString[$Output,$InstallationDirectory];Exit[]")

  private def findInstallDir(candidates: Seq[Path]): Option[Path] = {
    // On Windows, Mathematica/WolframEngine adds wolframscript.exe to the PATH.
    // On other platforms, wolframscript or wolfram might be on the PATH.
    // However, we can't rely on this, so we need to check the default install dirs too.
    //
    // We use wolfram instead of WolframKernel because it is meant for command-line use
    // while WolframKernel might spawn a GUI.
    // https://mathematica.stackexchange.com/a/84038

    installDirFromWolframscript().foreach(p => return Some(p))
    installDirFromWolfram().foreach(p => return Some(p))

    for (candidate <- candidates) {
      wolframscriptPath
        .map(candidate.resolve)
        .flatMap(p => installDirFromWolframscript(binary = p.toString))
        .foreach(p => return Some(p))

      wolframPath
        .map(candidate.resolve)
        .flatMap(p => installDirFromWolfram(binary = p.toString))
        .foreach(p => return Some(p))
    }

    None
  }

  def findMathematicaInstallDir(): Option[Path] = findInstallDir(defaultMathematicaInstallDirCandidates)

  def findWolframEngineInstallDir(): Option[Path] = findInstallDir(defaultWolframEngineInstallDirCandidates)

  /**
   * Find paths to specific files inside a Mathematica installation. Use [[findMathematicaInstallDir]] or
   * [[findWolframEngineInstallDir]] to find the installation itself.
   */
  def findMathematicaPaths(installDir: Path): Option[MathematicaPaths] = Some(MathematicaPaths(
    mathKernel = installDir.resolve(this.mathKernelPath.getOrElse(return None)),
    jlinkLib = installDir.resolve(this.jlinkLibPath.getOrElse(return None)),
  ))
}
