/*
 * Copyright (c) Carnegie Mellon University.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.helpers

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, BuiltInTactic}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.Augmentors._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tools.DefaultSMTConverter

import scala.collection.mutable.ListBuffer
import scala.io.Source

/**
  * Helper tools to log QE calls
  */
object QELogger {
  /* A simple measure of complexity on a first-order sequent
   - Used in QE logger to skip over trivial goals like 0 + 0 = 0
  */
  def measure(t:Term): Int = {
    t match {
      case _: Number => 0
      case _: AtomicTerm => 1
      case f: FuncOf => 1 + measure(f.child)
      case u: UnaryCompositeTerm => 1 + measure(u.child)
      case b: BinaryCompositeTerm => 1 + measure(b.left)+measure(b.right)
    }
  }

  def measure(f:Formula): Int = {
    f match {
      case c: ComparisonFormula => 1 + measure(c.left)+measure(c.right)
      case _: AtomicFormula => 1
      case u: UnaryCompositeFormula => 1 + measure(u.child)
      case b: BinaryCompositeFormula => 1 + measure(b.left) + measure(b.right)
      case q: Quantified => 1 + measure(q.child)
      // Not allowed in QE calls
      // case m: Modal => 1 + measure(m.program) + measure(m.child)
      // case p: PredOf => 1 + measure(p.child)
      // case p: PredicationalOf => 1 + measure(p.child)
    }
  }

  def measure(s:Sequent): Int = s.succ.map(measure).sum + s.ante.map(measure).sum

  /**
    *   A simple QE logging facility
    *   Each sequent is recorded together with the underlying conclusion of the provable that it is linked to
    *   # separates the conclusion and the actual sequent, @ separates lines
    *
    *   @ name_1 # Concl_1 # Seq_1
    *   @ name_2 # Concl_2 # Seq_2
    *   @ name_3 # Concl_3 # Seq_3
    *   ...
    *
    *   Sequents with the same name are grouped together when the file is re-parsed
    */
  private val defaultPath: String = Configuration.path(Configuration.Keys.QE_LOG_PATH)

  def clearLog(filename: String = defaultPath): Unit = {
    try {
      val f = scala.tools.nsc.io.File(filename)
      f.delete()
    } catch {
      case ex: Exception =>
        println("Failed to delete log")
        ex.printStackTrace()
    }
  }

  def logSequent(pr:Sequent,s:Sequent, name :String, filename:String = defaultPath): Unit = {
    try {
      val f = scala.tools.nsc.io.File(filename)
      val namestr = "@"+name+"#"+pr.toString+"#"+s.toString+"\n"
      f.appendAll(namestr)
    } catch {
      case ex: Exception =>
        println("Failed to record sequent")
        ex.printStackTrace()
    }
  }

  // Must be of the form Seq # Seq # Seq
  def parseStr(s:String): Option[(String,Sequent,Sequent)] = {
    val ss = s.split("#")
    if (ss.length != 3) None
    else try {
      val pr = ss(1).asSequent
      val seq = ss(2).asSequent
      Some(ss(0),pr,seq)
    } catch {
      case ex: Exception =>
        println("Failed to parse",s)
        ex.printStackTrace()
        None
    }
  }

  def parseLog(filename:String = defaultPath): Map[String,List[(Sequent,Sequent)]] = {
    // Upon reading @, save the previous sequent and provable
    var curString = ""

    var seqMap = new ListBuffer[(String,Sequent,Sequent)]()
    try {
      for (line <- Source.fromFile(filename).getLines()) {
        if (line.startsWith("@")) {
          parseStr(curString) match {
            case None => ()
            case Some(p) => seqMap += p
          }
          curString=line.substring(1)
        } else curString += line
      }
      parseStr(curString) match {
        case None => ()
        case Some(p) => seqMap += p
      }
    } catch {
      case ex: Exception =>
        println("File I/O exception")
        ex.printStackTrace()
    }
    seqMap.toList.groupBy(_._1).mapValues(_.map(p => (p._2,p._3)))
  }

  type LogConfig = (Int,String)
  private val defaultConf = (0, "")

  def measureRecordQE(lb: LogConfig = defaultConf): BuiltInTactic = new BuiltInTactic("logQE") {
      override def result(pr: ProvableSig): ProvableSig = {
        if (pr.subgoals.length == 1) {
          val sequent = pr.subgoals(0)
          if (measure(sequent) > lb._1)
            logSequent(pr.conclusion,sequent, lb._2)
        }
        pr
      }
    }

  private var logTactic = nil

  def getLogTactic: BelleExpr = logTactic

  //This bakes the recorder into the QE tactic, so it will record every single QE call, including internal ones made by
  //e.g. the ODE solver
  def enableLogging(loglevel: LogConfig = defaultConf ): Unit = {
    logTactic = measureRecordQE(loglevel)
  }

  def disableLogging(): Unit = {
    logTactic = nil
  }

  /** Exports the entries of `logPath` as separate files in SMT-Lib format to `exportPath` */
  def exportSmtLibFormat(logPath: String, exportPath: String): Unit = {
    val logEntries = parseLog(logPath)
    logEntries.foreach({case (name, sequents) =>
      val filePath = if (exportPath.contains("${entryname}")) exportPath else exportPath + "${entryname}"
      exportSmtLibFormat(sequents.head._2.toFormula, filePath.replace("${entryname}", name.replaceAll(" ", "_")))})
  }

  /** Exports the formula `fml` in SMT-Lib format to `exportFile`. */
  def exportSmtLibFormat(fml: Formula, exportFile: String): Unit = {
    val f = scala.tools.nsc.io.File(exportFile)
    f.appendAll(DefaultSMTConverter(fml))
  }

  def main(args: Array[String]): Unit = {
    val options = parseOptions(Map(), args.toList)
    options.get("convert") match {
      case Some(format) => format match {
        case "smtlib" =>
          val logPath = options.getOrElse("logpath", throw new Exception("Missing log file path, use argument -logpath path/to/logfile"))
          val outputPath = options.getOrElse("outputpath", logPath + "${entryname}.smt")
          exportSmtLibFormat(logPath, outputPath)
        case _ => throw new Exception("Unknown output format " + format + ", use one of [smtlib]")
      }
      case None => throw new Exception("Missing output format, use -convert smtlib")
    }
  }

  private def parseOptions(parsedOptions: Map[String, String], options: List[String]): Map[String, String] = options match {
    case Nil => parsedOptions
    case "-convert" :: value :: tail => parseOptions(parsedOptions ++ Map("convert" -> value), tail)
    case "-logpath" :: value :: tail => parseOptions(parsedOptions ++ Map("logpath" -> value), tail)
    case "-outputpath" :: value :: tail => parseOptions(parsedOptions ++ Map("outputpath" -> value), tail)
    case option :: tail => println("[Warning] Unknown option " + option + "\n\n"); parseOptions(parsedOptions, tail)
  }

}
