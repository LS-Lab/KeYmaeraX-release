package edu.cmu.cs.ls.keymaerax.fcpsutils

import java.io.File
import java.lang.Number
import java.util.Locale

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleProvable, SequentialInterpreter, BTacticParser}
import edu.cmu.cs.ls.keymaerax.btactics.{DifferentialTactics, NoneGenerate, TactixLibrary, DerivedAxioms}
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXProblemParser, ParseException}
import edu.cmu.cs.ls.keymaerax.tools.Mathematica

import scala.collection.immutable.Map

/**
  * @author Nathan Fulton
  */
object CourseMain {
  PrettyPrinter.setPrinter(edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter.pp)

  def main(input : Array[String]) = {
    val args : Map[String, ArgValue] = GetOpt(Map(
      "bparse" -> StrArgType(),
      "tparse" -> StrArgType(),
      "exists" -> StrArgType(),
      "problem" -> StrArgType(),
      "solution" -> StrArgType(),
      "is-exported-db" -> StrArgType()
    ))(input)

    try {
      args.foreach(pv => {
        val parameterName = pv._1
        val value = pv._2
        if (parameterName == "bparse") parseProblemFileOrFail(value)
        else if (parameterName == "tparse") parseTacticFileOrFail(value)
        else if (parameterName == "exists") fileExistsOrFail(value)
        else if (parameterName == "is-exported-db") isExportedDatabaseOrFail(value)
      })

      if(args.keySet.contains("problem") || args.keySet.contains("solution")) {
        val problemFile = args.getOrElse("problem",   throw new Exception("--problem and --solution flags should be both defined or both undefined."))
        val solutionFile = args.getOrElse("solution", throw new Exception("--problem and --solution flags should be both defined or both undefined."))
        isSolutionOrFail(problemFile, solutionFile)
      }

      System.exit(0)
    }
    catch {
      case e : Error => {
        e.printStackTrace()
        System.exit(-1)
      }
    }
  }

  private def isSolutionOrFail(problem: ArgValue, solution: ArgValue) = {
    val mathematica = new Mathematica()
    mathematica.init(defaultMathematicaConfig)
    val testFormula = Equal(edu.cmu.cs.ls.keymaerax.core.Number(1), edu.cmu.cs.ls.keymaerax.core.Number(1))
    assert(mathematica.qe(testFormula) == True, "Pre-grading sanity-check: MathematicaQE says 1 != 1 -- there's probably a problem with the Autograder.")

    DerivedAxioms.qeTool = mathematica
    TactixLibrary.tool = mathematica

    val f = parseProblemFileOrFail(problem)
    val expr = parseTacticFileOrFail(solution)

      try {
        val result = SequentialInterpreter(Seq())(expr, BelleProvable(Provable.startProof(f)))
        result match {
          case BelleProvable(p, _) => {
            if (!p.isProved) {
              println(s"Proof of ${fileExistsOrFail(problem)} using ${fileExistsOrFail(solution)} did not close. Remaining open goals follow:")
              println(p.prettyString)
              System.exit(-1)
            }
            else {
              println(s"Successfully proved ${fileExistsOrFail(problem)} using ${fileExistsOrFail(solution)}")
            }
          }
          case _ => throw new Exception("expected tactic execution to result in provable but found something else.")
        }
      } finally mathematica.shutdown()
  }

  /** Returns string contained within value */
  private def fileExistsOrFail(v : ArgValue) : String = {
    val fileName = v.asInstanceOf[StringValue].s
    assert({
      val file = new File(fileName)
      file.exists() && file.canRead()
    }, s"File named ${fileName} should exist and be readable.")
    fileName
  }

  private def parseTacticFileOrFail(v: ArgValue) = {
    val fileName = fileExistsOrFail(v)

    val mathematica = new Mathematica()
    mathematica.init(defaultMathematicaConfig)
    val testFormula = Equal(edu.cmu.cs.ls.keymaerax.core.Number(1), edu.cmu.cs.ls.keymaerax.core.Number(1))
    assert(mathematica.qe(testFormula) == True, "Pre-grading sanity-check: MathematicaQE says 1 != 1 -- there's probably a problem with the Autograder.")

    DerivedAxioms.qeTool = mathematica
    TactixLibrary.tool = mathematica

    BTacticParser(scala.io.Source.fromFile(new File(fileName)).mkString, false, Some(new NoneGenerate[Formula]())) match {
      case Some(e) => e
      case None => {
        println(s"Tactic in ${fileName} did not parse")
        System.exit(-1)
        ???
      }
    }
  }

  private def parseProblemFileOrFail(v: ArgValue) : Formula = {
    val fileName = fileExistsOrFail(v)
    try {
      edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser(scala.io.Source.fromFile(fileName).mkString)
    }
    catch {
      case e : ParseException => {
        println(s"Auto-grader failed because file ${fileName} needs to exist and parse but failed to parse.")
        e.printStackTrace()
        System.exit(-1)
        ???
      }
      case e : Error => {
        println(s"Unkown error encountered while parsing ${fileName}")
        System.exit(-1)
        ???
      }
    }
  }

  private def isExportedDatabaseOrFail(v : ArgValue) = {
    fileExistsOrFail(v)
  }


  //copy/paste
  def defaultMathematicaConfig: Map[String, String] = {
    if(defaultMathLinkPath._1 != "" && defaultMathLinkPath._2 != "") Map("linkName" -> defaultMathLinkPath._1, "libDir" -> defaultMathLinkPath._2)
    else throw new Exception("could not guess at the location of the MathKernel")
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
        // check if Mathematica version is 10.3
        if(new File(mathematicaWindowsPrefix + File.separator + "10.3").exists())
          mathematicaVersion = "10.3"
        // check if Mathematica version is 10.2
        else if(new File(mathematicaWindowsPrefix + File.separator + "10.2").exists())
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
}