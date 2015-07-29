package edu.cmu.cs.ls.keymaerax.launcher

import java.io.File
import java.util.Locale

import scala.collection.immutable.Map

/**
 * Created by smitsch on 7/14/15.
 * @author Stefan Mitsch
 * @author Ran Ji
 */
object DefaultConfiguration {

  def defaultMathLinkName: (String, String) = {
    var kernelName = ""
    var jlinkFileName = ""
    val osName = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)
    if(osName.contains("mac")) {
      kernelName = "MathKernel"
      jlinkFileName = "libJLinkNativeLibrary.jnilib"
    }
    else if(osName.contains("windows")) {
      kernelName = "MathKernel.exe"
      jlinkFileName = "JLinkNativeLibrary.dll"
    } else if(osName.contains("linux")) {
      kernelName = "MathKernel"
      jlinkFileName = "libJLinkNativeLibrary.so"
    }
    (kernelName, jlinkFileName)
  }

  def defaultMathematicaConfig: Map[String, String] = {
    if(defaultMathLinkPath._1 != "" && defaultMathLinkPath._2 != "") Map("linkName" -> defaultMathLinkPath._1, "libDir" -> defaultMathLinkPath._2)
    else Map()
  }

  def defaultMathLinkPath: (String, String) = {
    var linkNamePath: String = ""
    var libDirPath: String = ""
    val osName = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)
    val osArch = System.getProperty("os.arch")
    if(osName.contains("mac")) {
      val linkNamePathMac = "/Applications/Mathematica.app/Contents/MacOS/MathKernel"
      if(new File(linkNamePathMac).exists())
        linkNamePath = linkNamePathMac
      if(osArch.contains("64")) {
        val libDirPathMac64MmtcNew = "/Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86-64"
        val libDirPathMac64MmtcOld = "/Applications/Mathematica.app/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86-64"
        if (new File(libDirPathMac64MmtcNew).exists()) {
          libDirPath = libDirPathMac64MmtcNew
        } else if(new File(libDirPathMac64MmtcOld).exists()) {
          libDirPath = libDirPathMac64MmtcOld
        }
      } else {
        val libDirPathMac32MmtcNew = "/Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86"
        val libDirPathMac32MmtcOld = "/Applications/Mathematica.app/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86"
        if(new File(libDirPathMac32MmtcNew).exists()) {
          libDirPath = libDirPathMac32MmtcNew
        } else if(new File(libDirPathMac32MmtcOld).exists()) {
          libDirPath = libDirPathMac32MmtcOld
        }
      }
    } else if (osName.contains("windows")) {
      val mathematicaWindowsPrefix = "C:\\Program Files\\Wolfram Research\\Mathematica"
      var mathematicaVersion = ""

      if(new File(mathematicaWindowsPrefix).exists()) {
        // check if Mathematica version is 10.2
        if(new File(mathematicaWindowsPrefix + File.separator + "10.2").exists())
          mathematicaVersion = "10.2"
        // check if Mathematica version is 10.1
        else if(new File(mathematicaWindowsPrefix + File.separator + "10.1").exists())
          mathematicaVersion = "10.1"
        else {
          // check if Mathematica version is any of 6.0, 7.0, 8.0, 9.0 or 10.0
          for(i <- 6 to 10) {
            if(new File(mathematicaWindowsPrefix + File.separator + i.toString + ".0").exists())
              mathematicaVersion = i.toString + ".0"
          }
        }
        if(mathematicaVersion!="") {
          val linkNamePathWindows = mathematicaWindowsPrefix + File.separator + mathematicaVersion + File.separator + "MathKernel.exe"
          if(new File(linkNamePathWindows).exists())
            linkNamePath = linkNamePathWindows
          if (osArch.contains("64")) {
            val libDirPathWindows64 =  mathematicaWindowsPrefix + File.separator + mathematicaVersion + File.separator + "SystemFiles\\Links\\JLink\\SystemFiles\\Libraries\\Windows-x86-64"
            if(new File(libDirPathWindows64).exists())
              libDirPath = libDirPathWindows64
          } else {
            val libDirPathWindows32 =  mathematicaWindowsPrefix + File.separator + mathematicaVersion + File.separator + "SystemFiles\\Links\\JLink\\SystemFiles\\Libraries\\Windows"
            if(new File(libDirPathWindows32).exists())
              libDirPath = libDirPathWindows32
          }
        }
      }

    } else if(osName.contains("linux")) {
      val mathematicaLinuxPrefix = "/usr/local/Wolfram/Mathematica"
      var mathematicaVersion = ""
      if(new File(mathematicaLinuxPrefix).exists()) {
        // check if Mathematica version is 10.2
        if(new File(mathematicaLinuxPrefix + File.separator + "10.2").exists())
          mathematicaVersion = "10.2"
        // check if Mathematica version is 10.1
        else if(new File(mathematicaLinuxPrefix + File.separator + "10.1").exists())
          mathematicaVersion = "10.1"
        else {
          // check if Mathematica version is any of 6.0, 7.0, 8.0, 9.0 or 10.0
          for(i <- 6 to 10) {
            if(new File(mathematicaLinuxPrefix + File.separator + i.toString + ".0").exists())
              mathematicaVersion = i.toString + ".0"
          }
        }
        if(mathematicaVersion != "") {
          val linkNamePathLinux = mathematicaLinuxPrefix + File.separator + mathematicaVersion + File.separator + "Executables/MathKernel"
          if(new File(linkNamePathLinux).exists())
            linkNamePath = linkNamePathLinux
          if(osArch.contains("64")) {
            val libDirPathLinux64 = mathematicaLinuxPrefix + File.separator + mathematicaVersion + File.separator + "SystemFiles/Links/JLink/SystemFiles/Libraries/Linux-x86-64"
            if(new File(libDirPathLinux64).exists())
              libDirPath = libDirPathLinux64
          } else {
            val libDirPathLinux32 = mathematicaLinuxPrefix + File.separator + mathematicaVersion + File.separator + "SystemFiles/Links/JLink/SystemFiles/Libraries/Linux"
            if(new File(libDirPathLinux32).exists())
              libDirPath = libDirPathLinux32
          }
        }
      }
    }
    (linkNamePath, libDirPath)
  }

  def exemplaryMathLinkPath: (String, String) = {
    var linkNamePath: String = ""
    var libDirPath: String = ""
    val osName = System.getProperty("os.name").toLowerCase(Locale.ENGLISH)
    val osArch = System.getProperty("os.arch")
    if(osName.contains("mac")) {
      linkNamePath = "/Applications/Mathematica.app/Contents/MacOS/MathKernel"
      if(osArch.contains("64")) {
        libDirPath = "/Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86-64"
      } else libDirPath = "/Applications/Mathematica.app/Contents/SystemFiles/Links/JLink/SystemFiles/Libraries/MacOSX-x86"
    } else if(osName.contains("windows")) {
      linkNamePath = "C:\\Program Files\\Wolfram Research\\Mathematica\\10.0\\MathKernel.exe"
      if(osArch.contains("64")) {
        libDirPath = "C:\\Program Files\\Wolfram Research\\Mathematica\\10.0\\SystemFiles\\Links\\JLink\\SystemFiles\\Libraries\\Windows-x86-64"
      } else libDirPath = "C:\\Program Files\\Wolfram Research\\Mathematica\\10.0\\SystemFiles\\Links\\JLink\\SystemFiles\\Libraries\\Windows"
    } else if(osName.contains("linux")) {
      linkNamePath = "/usr/local/Wolfram/Mathematica/10.0/Executables/MathKernel"
      if(osArch.contains("64")) {
        libDirPath = "/usr/local/Wolfram/Mathematica/10.0/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux-x86-64"
      } else libDirPath = "/usr/local/Wolfram/Mathematica/10.0/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux"
    }
    (linkNamePath, libDirPath)
  }
}
