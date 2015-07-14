package edu.cmu.cs.ls.keymaerax.launcher

import java.util.Locale

import scala.collection.immutable.Map

/**
 * Created by smitsch on 7/14/15.
 * @author Stefan Mitsch
 * @author Ran Ji
 */
object DefaultConfiguration {

  def defaultMathematicaConfig: Map[String, String] = {
    var linkNamePath: String = ""
    var libDirPath: String = ""
    val osName = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)
    val osArch = System.getProperty("os.arch")
    if (osName.contains("mac")) {
      val linkNamePathMac = "/Applications/Mathematica.app/Contents/MacOS/MathKernel"
      if(new java.io.File(linkNamePathMac).exists())
        linkNamePath = linkNamePathMac
      if (osArch.contains("64")) {
        val libDirPathMac64MmtcNew = "/Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86-64"
        val libDirPathMac64MmtcOld = "/Applications/Mathematica.app/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86-64"
        if (new java.io.File(libDirPathMac64MmtcNew).exists()) {
          libDirPath = libDirPathMac64MmtcNew
        } else if(new java.io.File(libDirPathMac64MmtcOld).exists()) {
          libDirPath = libDirPathMac64MmtcOld
        }
      } else {
        val libDirPathMac32MmtcNew = "/Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86"
        val libDirPathMac32MmtcOld = "/Applications/Mathematica.app/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86"
        if (new java.io.File(libDirPathMac32MmtcNew).exists()) {
          libDirPath = libDirPathMac32MmtcNew
        } else if(new java.io.File(libDirPathMac32MmtcOld).exists()) {
          libDirPath = libDirPathMac32MmtcOld
        }
      }
    } else if (osName.contains("windows")) {
      val linkNamePathWindows = "C:\\Program Files\\Wolfram Research\\Mathematica\\10.0\\MathKernel.exe"
      if (new java.io.File(linkNamePathWindows).exists())
        linkNamePath = linkNamePathWindows
      if (osArch.contains("64")) {
        val libDirPathWindows64 = "C:\\Program Files\\Wolfram Research\\Mathematica\\10.0\\SystemFiles\\Links\\JLink\\SystemFiles\\Libraries\\Windows-x86-64"
        if(new java.io.File(libDirPathWindows64).exists())
          libDirPath = libDirPathWindows64
      } else {
        val libDirPathWindows32 = "C:\\Program Files\\Wolfram Research\\Mathematica\\10.0\\SystemFiles\\Links\\JLink\\SystemFiles\\Libraries\\Windows"
        if(new java.io.File(libDirPathWindows32).exists())
          libDirPath = libDirPathWindows32
      }
    } else if (osName.contains("linux")) {
      val linkNamePathLinuxMmtc10 = "/usr/local/Wolfram/Mathematica/10.0/Executables/MathKernel"
      val linkNamePathLinuxMmtc9 = "/usr/local/Wolfram/Mathematica/9.0/Executables/MathKernel"
      if (new java.io.File(linkNamePathLinuxMmtc10).exists()) {
        linkNamePath = linkNamePathLinuxMmtc10
        if (osArch.contains("64")) {
          val libDirPathLinux64Mmtc10 = "/usr/local/Wolfram/Mathematica/10.0/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux-x86-64"
          if (new java.io.File(libDirPathLinux64Mmtc10).exists())
            libDirPath = libDirPathLinux64Mmtc10
        } else {
          val libDirPathLinux32Mmtc10 = "/usr/local/Wolfram/Mathematica/10.0/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux"
          if(new java.io.File(libDirPathLinux32Mmtc10).exists())
            libDirPath = libDirPathLinux32Mmtc10
        }
      } else if (new java.io.File(linkNamePathLinuxMmtc9).exists()) {
        linkNamePath = linkNamePathLinuxMmtc9
        if (osArch.contains("64")) {
          val libDirPathLinux64Mmtc9 = "/usr/local/Wolfram/Mathematica/9.0/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux-x86-64"
          if(new java.io.File(libDirPathLinux64Mmtc9).exists())
            libDirPath = libDirPathLinux64Mmtc9
        } else {
          val libDirPathLinux32Mmtc9 = "/usr/local/Wolfram/Mathematica/9.0/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux"
          if(new java.io.File(libDirPathLinux32Mmtc9).exists())
            libDirPath = libDirPathLinux32Mmtc9
        }
      }
    }
    if (linkNamePath != "" && libDirPath != "") Map("linkName" -> linkNamePath, "libDir" -> libDirPath)
    else Map()
  }

}
