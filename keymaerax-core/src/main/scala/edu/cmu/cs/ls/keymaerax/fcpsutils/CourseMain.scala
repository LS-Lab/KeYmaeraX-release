package edu.cmu.cs.ls.keymaerax.fcpsutils

import java.io.File
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.GenProduct
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core.Formula
import edu.cmu.cs.ls.keymaerax.parser.{Declaration, ParseException, ParsedArchiveEntry}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool

/**
  * @author Nathan Fulton
  */
object CourseMain {
  /** Just enough initialization. */
  def basicInitializer() = {
    // This initializes Mathematica (falling back to Z3 on failure)
    // Commented out because it is otherwise very verbose on Autolab
    //    try {
    //      val config = Map(
    //        // Local paths
    //        //"linkName" -> "/usr/local/Wolfram/Mathematica/11.3/Executables/MathKernel",
    //        //"libDir" -> "/usr/local/Wolfram/Mathematica/11.3/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux-x86-64")
    //        // These paths might (?) work on autograding machines
    //        "linkName" -> "/usr/local/depot/mathematica-11.3/Executables/MathKernel",
    //        "libDir" -> "/usr/local/depot/mathematica-11.3/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux-x86-64")
    //      val provider = new MathematicaToolProvider(config)
    //      ToolProvider.setProvider(provider)
    //      BelleInterpreter.setInterpreter(ExhaustiveSequentialInterpreter())
    //      if(provider.tools().forall(_.isInitialized)) println("Initialized Mathematica!")
    //      else println("Not initialized, but without any errors -- won't be able to parse tactics or check proofs.")
    //    } catch {
    //      case _: Throwable => {
    //        println("Falling back to Z3. Not a big deal but some features won't be available.")
    //        val provider = new Z3ToolProvider()
    //        ToolProvider.setProvider(provider)
    //        BelleInterpreter.setInterpreter(ExhaustiveSequentialInterpreter())
    //        if(provider.tools().forall(_.isInitialized)) println("Initialized Z3!")
    //      }
    //    }

    println("Falling back to Z3. Not a big deal but some features won't be available.")
    val provider = new Z3ToolProvider()
    ToolProvider.setProvider(provider)
    if(provider.tools().forall(_.isInitialized)) println("Initialized Z3!")
    KeYmaeraXTool.init(Map(
      KeYmaeraXTool.INIT_DERIVATION_INFO_REGISTRY -> "true",
      KeYmaeraXTool.INTERPRETER -> LazySequentialInterpreter.getClass.getSimpleName
    ))
  }

  /** A command-line tool that doesn't contain any of the web UI stuff. Useful because the JAR is considerably smaller, but many features aren't available.
    * You probably want to use KeYmaeraX.scala instead of this, unless you're setting up an AutoLab sanity checker.*/
  def main(input : Array[String]) = {
    basicInitializer()

    val args : Map[String, ArgValue] = GetOpt(Map(
      "check" -> StrArgType(),
      "parse" -> StrArgType(),
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
        // Parse and automatically check an archive file
        if (parameterName == "check") parseCheck(value,true)
        // Parse an archive file only
        else if (parameterName == "parse") parseCheck(value,false)
        // Parse a .kyx file only
        else if (parameterName == "bparse") parseProblemFileOrFail(value)
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
        println("Error propagated to top level")
        e.printStackTrace()
        System.exit(-1)
      }
    }
  }

  private def parseCheck(archiveFile : ArgValue, doCheck : Boolean) = {
    val archiveFileStr = archiveFile.asInstanceOf[StringValue].s

    try {
      val archiveEntries : List[ParsedArchiveEntry] = try {
        parseArchiveFileOrfail(archiveFile)
      } catch {
        case e : Throwable => {
          println(s"Expected a valid .kyx file but could not parse file contents: ${archiveFileStr}")
          System.exit(-1)
          Nil
        }
      }

      if(archiveEntries.length != 1) {
        println("Expected an archive file with exactly one model. Did you export a single proof from the Proofs page?")
        System.exit(-1)
      }
      else if(archiveEntries.head.tactics.length != 1) {
        println("Expected an archive file with exactly one model and exactly one proof. Did you export a single proof from the Proofs page?")
        System.exit(-1)
      }

      println(s"Archive file ${archiveFileStr} parsed successfully.")

      if (doCheck) {
        val f = archiveEntries.head.model.asInstanceOf[Formula]
        val expr = archiveEntries.head.tactics.head._3
        /*val f = parseProblemFileOrFail(problem)*/
        /*val expr = parseTacticFileOrFail(solution)*/

        val result = BelleInterpreter(expr, BelleProvable(ProvableSig.startProof(f), None, Declaration(Map.empty)))
        result match {
          case BelleProvable(p, _, _) => {
            if(!p.isProved) {
              println(s"ERROR: ${archiveFileStr} proof did not close on grading machine:")
              println(p.prettyString)
              System.exit(-1)
            }
            else {
              println(s"Archive file ${archiveFileStr} checked successfully.")
              System.exit(0)
            }
          }
          case _ => throw new Exception("expected tactic execution to result in provable but found something else.")
        }
      }
      else {
        println(s"Proof checking for ${archiveFileStr} skipped.")
      }
    } catch {case e : Any =>
      println(s"ERROR:Exception when parsing / checking ${archiveFileStr} on grading machine:" + e)
      System.exit(-1)
    }
  }

  private def isSolutionOrFail(problem: ArgValue, solution: ArgValue) = {
    val f = parseProblemFileOrFail(problem)
    val expr = parseTacticFileOrFail(solution)

    val result = BelleInterpreter(expr, BelleProvable(ProvableSig.startProof(f), None, Declaration(Map.empty)))
    result match {
      case BelleProvable(p, _, _) => {
        if(!p.isProved) {
          println(s"Proof of ${fileExistsOrFail(problem)} using ${fileExistsOrFail(solution)} did not close. Remaining open goals follow:")
          println(p.prettyString)
          System.exit(-1)
        }
      }
      case _ => throw new Exception("expected tactic execution to result in provable but found something else.")
    }
  }

  /** Returns string contained within value */
  private def fileExistsOrFail(v : ArgValue) : String = {
    val fileName = v.asInstanceOf[StringValue].s
    print("Looking for " + fileName + "\n")
    assert({
      val file = new File(fileName)
      file.exists() && file.canRead()
    }, s"File named ${fileName} should exist and be readable.")
    fileName
  }

  private def parseTacticFileOrFail(v: ArgValue): BelleExpr = {
    val fileName = fileExistsOrFail(v)
    val bigString = scala.io.Source.fromFile(fileName, "ISO-8859-1").mkString
    try {
      BelleParser.parseWithInvGen(bigString, Some(FixedGenerator[GenProduct](Nil)))
    } catch {
      case ex: ParseException =>
        println(s"Tactic in ${fileName} did not parse\n" + ex)
        System.exit(-1)
        ???
    }
  }

  private def parseArchiveFileOrfail(v: ArgValue) : List[ParsedArchiveEntry] = {
    val fileName = fileExistsOrFail(v)
    val bigString = scala.io.Source.fromFile(fileName, "ISO-8859-1").mkString
    try {
      edu.cmu.cs.ls.keymaerax.parser.ArchiveParser.parse(bigString)
    }
    catch {
      case e : ParseException => {
        println(s"Auto-grader failed because file ${fileName} needs to exist and parse but failed to parse.")
        e.printStackTrace()
        System.exit(-1)
        ???
      }
      case e : Throwable => {
        println(s"Unkown error encountered while parsing ${fileName}: ${e}\nContents${bigString}")
        e.printStackTrace()
        System.exit(-1)
        ???
      }
    }
  }

  private def parseProblemFileOrFail(v: ArgValue) : Formula = {
    val fileName = fileExistsOrFail(v)
    val bigString = scala.io.Source.fromFile(fileName, "ISO-8859-1").mkString
    try {
      val fml = edu.cmu.cs.ls.keymaerax.parser.ArchiveParser.parseAsFormula(bigString)
      println(s"Problem file ${fileName} parsed successfully.")
      fml
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
}
