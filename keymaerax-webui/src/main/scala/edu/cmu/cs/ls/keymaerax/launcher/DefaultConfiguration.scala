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

  /** The Mathematica config as set from the command line (default config if not set) */
  var currentMathematicaConfig: Map[String, String] = defaultMathematicaConfig

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

  /** Assumes that directory is a directory that contains subdirectory for each installed version of Mathematica.
    * Returns the largest version of Mathematica that has an installation directory if one exists. Else returns the empty string. */
  private def findLargestSubdirectory(dir: File) = {
    assert(dir.isDirectory, s"Expected a directory but found something else @ ${dir.getAbsolutePath}")
    val largestAvailableVersion = dir.listFiles().map(f =>
      try {
        java.lang.Double.parseDouble(f.getName)
      } catch {
        case _:Exception => -1
      }
    ).max

    if(largestAvailableVersion == -1)
      ""
    else
      largestAvailableVersion.toString
  }
  //@todo this code should be re-written. First identify the prefix/suffix for the system, and then figure out the version. Otherwise we have to update N places in the code every time a new version of Mathematica is released.
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
    }
    else if (osName.contains("windows")) {
      val mathematicaWindowsPrefix = "C:\\Program Files\\Wolfram Research\\Mathematica"
      var mathematicaVersion = ""

      val versionsDir = new File(mathematicaWindowsPrefix)
      if(versionsDir.exists())
        mathematicaVersion = findLargestSubdirectory(versionsDir)

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

    else if(osName.contains("linux")) {
      val mathematicaLinuxPrefix = "/usr/local/Wolfram/Mathematica"
      var mathematicaVersion = ""
      val installedMathematicas = new File(mathematicaLinuxPrefix)
      if(installedMathematicas.exists())
        mathematicaVersion = findLargestSubdirectory(installedMathematicas)

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

    (linkNamePath, libDirPath)
  }

  def exemplaryMathLinkPath: (String, String) = {
    val MATHEMATICA_VERSION = "11.0"
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
      linkNamePath = s"C:\\Program Files\\Wolfram Research\\Mathematica\\${MATHEMATICA_VERSION}\\MathKernel.exe"
      if(osArch.contains("64")) {
        libDirPath = s"C:\\Program Files\\Wolfram Research\\Mathematica\\${MATHEMATICA_VERSION}\\SystemFiles\\Links\\JLink\\SystemFiles\\Libraries\\Windows-x86-64"
      } else libDirPath = s"C:\\Program Files\\Wolfram Research\\Mathematica\\${MATHEMATICA_VERSION}\\SystemFiles\\Links\\JLink\\SystemFiles\\Libraries\\Windows"
    } else if(osName.contains("linux")) {
      linkNamePath = s"/usr/local/Wolfram/Mathematica/${MATHEMATICA_VERSION}/Executables/MathKernel"
      if(osArch.contains("64")) {
        libDirPath = s"/usr/local/Wolfram/Mathematica/${MATHEMATICA_VERSION}/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux-x86-64"
      } else libDirPath = s"/usr/local/Wolfram/Mathematica/${MATHEMATICA_VERSION}/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux"
    }
    (linkNamePath, libDirPath)
  }
}
