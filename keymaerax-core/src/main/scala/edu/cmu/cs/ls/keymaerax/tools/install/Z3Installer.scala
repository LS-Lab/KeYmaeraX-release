/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools.install

import edu.cmu.cs.ls.keymaerax.info.{ArchType, Os, OsType, Version, VersionNumber}
import edu.cmu.cs.ls.keymaerax.{Configuration, Logging}

import java.io.{File, FileOutputStream, InputStream, PrintWriter}
import java.nio.channels.Channels

/** Installs and/or updates the Z3 binary in the KeYmaera X directory. */
object Z3Installer extends Logging {
  val z3FileName: String = Os.Type match {
    case OsType.Windows => "z3.exe"
    case _ => "z3"
  }

  /** The default z3 installation path. */
  val defaultZ3Path: String = { Configuration.KEYMAERAX_HOME_PATH + File.separator + z3FileName }

  /**
   * Get the absolute path to the Z3 binary. Installs Z3 from the JAR if not installed yet, or if the KeYmaera X version
   * has updated.
   */
  val z3Path: String = {
    val z3ConfigPath = Configuration.path(Configuration.Keys.Z3_PATH)
    val z3Path = if (new File(z3ConfigPath).exists) z3ConfigPath else defaultZ3Path
    val z3File = if (new File(z3Path).isFile) new File(z3Path) else new File(z3Path + File.separator + z3FileName)
    if (!z3File.getParentFile.exists) z3File.mkdirs

    val needsUpdate = !installedFromKyxVersion(defaultZ3Path).contains(Version)
    val z3AbsPath =
      if (z3ConfigPath == defaultZ3Path && needsUpdate) {
        logger.debug("Updating default Z3 binary...")
        new File(copyToDisk(new File(defaultZ3Path).getParent))
      } else if (z3File.exists()) { z3File }
      else {
        logger.debug("Installing Z3 binary...")
        new File(copyToDisk(z3File.getParent))
      }

    assert(z3AbsPath.exists())
    z3AbsPath.getAbsolutePath
  }

  /**
   * We store the last version of KeYmaera X that updated the Z3 binary, and copy over Z3 every time we notice a new
   * version of KeYmaera X is installed.
   * @todo
   *   We should probably check the Z3 version instead but...
   */
  def versionFile(z3TempDir: String): File = new File(z3TempDir + File.separator + "z3v")

  /**
   * Returns the KeYmaera X version that supplied the currently installed Z3, or [[None]] if it could not be determined.
   */
  def installedFromKyxVersion(z3TempDir: String): Option[VersionNumber] = {
    if (versionFile(z3TempDir).exists()) {
      val source = scala.io.Source.fromFile(versionFile(z3TempDir))
      val result = source.mkString
      source.close()
      Some(VersionNumber.parse(result))
    } else {
      None // Return no version number, forcing Z3 to be copied to disk.
    }
  }

  /** Copies Z3 to the disk. Returns the path to the binary. */
  def copyToDisk(z3TempDir: String): String = {
    // Update the version number.
    new PrintWriter(versionFile(z3TempDir)) { write(Version.toString); close() }
    // Copy z3 binary to disk.
    val resource: InputStream = (Os.Type, Os.JvmArchType) match {
      case (OsType.Windows, ArchType.Bit32) => this.getClass.getResourceAsStream("/z3/windows32/z3.exe")
      case (OsType.Windows, ArchType.Bit64) => this.getClass.getResourceAsStream("/z3/windows64/z3.exe")
      case (OsType.Linux, ArchType.Bit64) => this.getClass.getResourceAsStream("/z3/ubuntu64/z3")
      case (OsType.MacOs, ArchType.Bit64) => this.getClass.getResourceAsStream("/z3/mac64/z3")
      case (OsType.Unknown, _) => throw new Exception("Z3 solver is currently not supported in your operating system.")
      case _ => null
    }
    if (resource == null) {
      val z3 = new File(z3TempDir + File.separator + "z3")
      if (!z3.exists)
        throw new Exception("Could not find Z3 in classpath jar bundle: " + System.getProperty("user.dir"))
      else {
        val z3AbsPath = z3.getAbsolutePath

        val permissionCmd = Os.Type match {
          case OsType.Windows => Array("icacls", z3AbsPath, "/e", "/p", "Everyone:F")
          case _ => Array("chmod", "u+x", z3AbsPath)
        }
        Runtime.getRuntime.exec(permissionCmd)

        return z3AbsPath
      }
    }
    val z3Source = Channels.newChannel(resource)
    val z3Temp = new File(z3TempDir, z3FileName)

    // Get a stream to the script in the resources dir
    val z3Dest = new FileOutputStream(z3Temp)
    // Copy file to temporary directory
    z3Dest.getChannel.transferFrom(z3Source, 0, Long.MaxValue)
    val z3AbsPath = z3Temp.getAbsolutePath

    val permissionCmd = Os.Type match {
      case OsType.Windows => Array("icacls", z3AbsPath, "/e", "/p", "Everyone:F")
      case _ => Array("chmod", "u+x", z3AbsPath)
    }
    // @todo Could change to only modify permissions of freshly extracted files not from others that happen to preexist. It's in KeYmaera's internal folders, though.
    Runtime.getRuntime.exec(permissionCmd)

    z3Source.close()
    z3Dest.close()
    assert(new File(z3AbsPath).exists())
    z3AbsPath
  }

}
