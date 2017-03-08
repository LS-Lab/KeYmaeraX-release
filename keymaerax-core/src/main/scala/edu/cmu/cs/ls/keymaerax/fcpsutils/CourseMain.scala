package edu.cmu.cs.ls.keymaerax.fcpsutils

import java.io.File

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BelleProvable, SequentialInterpreter}
import edu.cmu.cs.ls.keymaerax.btactics._
import edu.cmu.cs.ls.keymaerax.core.{Formula, PrettyPrinter, Program}
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXArchiveParser, KeYmaeraXParser, ParseException}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig

/**
  * @author Nathan Fulton
  */
object CourseMain {
  /** Just enough initialization. */
  def basicInitializer() = {
    try {
      val config = Map(
        "linkName" -> "/usr0/local/Wolfram/Mathematica/10.0/Executables/MathKernel",
        "libDir" -> "/usr0/local/Wolfram/Mathematica/10.0/SystemFiles/Links/JLink/SystemFiles/Libraries/Linux-x86-64")
      val provider = new MathematicaToolProvider(config)
      ToolProvider.setProvider(provider)
      if(provider.tools().forall(_.isInitialized)) println("Initialized!")
      else println("Not initialized, but without any errors -- won't be able to parse tactics or check proofs.")
    } catch {
      case _: Throwable => {
        println("Falling back to Z3. Not a big deal but some features won't be available.")
        ToolProvider.setProvider(new Z3ToolProvider())
      }
    }

    //Intialize the printer, the configuration generator, the parser, and the invariant generator.
    PrettyPrinter.setPrinter(edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter.pp)
    val generator = new ConfigurableGenerator[Formula]()
    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) => generator.products += (p->inv))
    TactixLibrary.invGenerator = generator
  }

  /** A command-line tool that doesn't contain any of the web UI stuff. Useful because the JAR is considerably smaller, but many features aren't available.
    * You probably want to use KeYmaeraX.scala instead of this, unless you're setting up an AutoLab sanity checker. */
  def main(input : Array[String]) = {
    basicInitializer()

    val args : Map[String, ArgValue] = GetOpt(Map(
      "check" -> StrArgType(),
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
        if (parameterName == "check") check(value)
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

  private def check(archiveFile : ArgValue) = {
    val archiveEntries : List[KeYmaeraXArchiveParser.ParsedArchiveEntry] = try {
      parseArchiveFileOrfail(archiveFile)
    } catch {
      case e : Throwable => {
        println(s"Expected a valid .kya file but could not parse file contents: ${archiveFile}")
        System.exit(-1)
        Nil
      }
    }

    if(archiveEntries.length != 1) {
      println("Expected an archive file with exactly one model. Did you export a single proof from the Proofs page?")
      System.exit(-1)
    }
    else if(archiveEntries.head._4.length != 1) {
      println("Expected an archive file with exactly one model and exactly one proof. Did you export a single proof from the Proofs page?")
      System.exit(-1)
    }
    else {
      val f = archiveEntries.head._3.asInstanceOf[Formula]
      val expr = archiveEntries.head._4.head._2
      /*val f = parseProblemFileOrFail(problem)*/
      /*val expr = parseTacticFileOrFail(solution)*/

        val result = SequentialInterpreter(Seq())(expr, BelleProvable(ProvableSig.startProof(f)))
        result match {
          case BelleProvable(p, _) => {
            if(!p.isProved) {
              println(s"ERROR: " + archiveFile + " Proof did not close on grading machine:")
              println(p.prettyString)
              System.exit(-1)
            }
          }
          case _ => throw new Exception("expected tactic execution to result in provable but found something else.")
        }
      }
    } catch {case e : Any =>
      println(s"ERROR:Exception during " + archiveFile + " proof on grading machine")
      System.exit(-1)
    }
  }

  private def isSolutionOrFail(problem: ArgValue, solution: ArgValue) = {
    val f = parseProblemFileOrFail(problem)
    val expr = parseTacticFileOrFail(solution)

    val result = SequentialInterpreter(Seq())(expr, BelleProvable(ProvableSig.startProof(f)))
    result match {
      case BelleProvable(p, _) => {
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
    try {
      BelleParser.parseWithInvGen(scala.io.Source.fromFile(new File(fileName)).mkString, Some(FixedGenerator[Formula](Nil)))
    } catch {
      case ex: ParseException =>
        println(s"Tactic in ${fileName} did not parse\n" + ex)
        System.exit(-1)
        ???
    }
  }

  private def parseArchiveFileOrfail(v: ArgValue) : List[KeYmaeraXArchiveParser.ParsedArchiveEntry] = {
    val fileName = fileExistsOrFail(v)
    val bigString = scala.io.Source.fromFile(fileName, "ISO-8859-1").mkString
    try {
      edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXArchiveParser.parse(bigString)
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
}
