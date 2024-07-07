/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics.helpers

import java.io.FileWriter
import org.keymaerax.{Configuration, FileConfiguration, Logging}
import org.keymaerax.bellerophon.{BelleExpr, BuiltInTactic}
import org.keymaerax.btactics.TactixLibrary._
import org.keymaerax.infrastruct.Augmentors._
import org.keymaerax.core._
import org.keymaerax.parser.KeYmaeraXPrettyPrinter
import org.keymaerax.parser.StringConverter._
import org.keymaerax.pt.ProvableSig
import org.keymaerax.tools.qe.DefaultSMTConverter

import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer
import scala.io.Source

/**
 * A simple QE logging facility Each sequent is recorded together with the underlying conclusion of the provable that it
 * is linked to `#` separates the conclusion and the actual sequent, `@` separates lines
 *
 * {{{
 *   @ name_1 # Concl_1 # Seq_1
 *   @ name_2 # Concl_2 # Seq_2
 *   @ name_3 # Concl_3 # Seq_3
 *   ...
 * }}}
 *
 * Sequents with the same name are grouped together when the file is re-parsed
 */
object QELogger extends Logging {

  /* A simple measure of complexity on a first-order sequent
   - Used in QE logger to skip over trivial goals like 0 + 0 = 0
   */
  def measure(t: Term): Int = {
    t match {
      case _: Number => 0
      case _: AtomicTerm => 1
      case f: FuncOf => 1 + measure(f.child)
      case u: UnaryCompositeTerm => 1 + measure(u.child)
      case b: BinaryCompositeTerm => 1 + measure(b.left) + measure(b.right)
    }
  }

  def measure(f: Formula): Int = {
    f match {
      case c: ComparisonFormula => 1 + measure(c.left) + measure(c.right)
      case _: AtomicFormula => 1
      case u: UnaryCompositeFormula => 1 + measure(u.child)
      case b: BinaryCompositeFormula => 1 + measure(b.left) + measure(b.right)
      case q: Quantified => 1 + measure(q.child)
      // Not allowed in QE calls
      case m: Modal =>
        throw new IllegalArgumentException("Modalities cannot occur in real arithmetic quantifier elimination: " + f)
      // case p: PredOf => 1 + measure(p.child)
      // case p: PredicationalOf => 1 + measure(p.child)
    }
  }

  def measure(s: Sequent): Int = s.succ.map(measure).sum + s.ante.map(measure).sum

  /** Default path from the configuration. */
  private lazy val defaultPath: String = Configuration.path(Configuration.Keys.QE_LOG_PATH)

  /** Returns a default 'qe.txt' file if path points to a directory, the path file otherwise. */
  private def file(filename: String): java.io.File =
    if (new java.io.File(filename).isDirectory) { new java.io.File(filename, "qe.txt") }
    else { new java.io.File(filename) }

  /** Deletes the log file at `path`. */
  def clearLog(path: String = defaultPath): Unit = {
    try {
      val f = file(path)
      f.delete()
    } catch { case ex: Exception => logger.error("Failed to delete log", ex) }
  }

  /** Appends the conclusion `pr` and the goal `s` under `name` to the file at `path`. */
  def logSequent(pr: Sequent, s: Sequent, name: String, filename: String = defaultPath): Unit = {
    try {
      val f = file(filename)
      val parent = f.getParentFile
      if (parent != null) parent.mkdirs()
      // @note opening and closing file on every write negligible to cost of contract-checking Sequent.toString
      val namestr = "@" + name + "#" + pr.toString + "#" + s.toString + "\n"
      val fw = new FileWriter(f, true)
      fw.append(namestr)
      fw.close()
    } catch { case ex: Exception => logger.error("Failed to record sequent", ex) }
  }

  /** Parses string `s` of the form Name # Seq # Seq; returns None if not of that form. */
  def parseStr(s: String): Option[(String, Sequent, Sequent)] = {
    val ss = s.split("#")
    if (ss.length != 3) None
    else
      try {
        val pr = ss(1).asSequent
        val seq = ss(2).asSequent
        Some(ss(0), pr, seq)
      } catch {
        case ex: Exception =>
          logger.error("Failed to parse " + s, ex)
          None
      }
  }

  /** Parses string `s` of the form Name # Seq-1 # Seq-2; returns Some(Name, Seq-2), or None if not of that form. */
  def parseStr2(s: String): Option[(String, Sequent)] = {
    val ss = s.split("#")
    if (ss.length != 3) None
    else
      try { Some(ss(0), ss(2).asSequent) }
      catch {
        case ex: Exception =>
          logger.error("Failed to parse " + s, ex)
          None
      }
  }

  /** Parses the log into a map (reads large log files into memory!). */
  def parseLog(filename: String = defaultPath): Map[String, List[(Sequent, Sequent)]] = {
    class LogCollector extends (((String, Sequent, Sequent)) => Unit) {
      val entries: ListBuffer[(String, Sequent, Sequent)] = new ListBuffer[(String, Sequent, Sequent)]()
      def apply(e: (String, Sequent, Sequent)): Unit = entries += e
    }

    val c = new LogCollector()
    processLog(parseStr, c, filename)
    c.entries.toList.groupBy(_._1).view.mapValues(_.map(p => (p._2, p._3))).toMap
  }

  /** Process log one entry at a time. */
  def processLog[T](parseEntry: String => Option[T], processEntry: T => Unit, filename: String = defaultPath): Unit = {
    // Upon reading @, save the previous sequent and provable
    var curString = ""

    val src = Source.fromFile(file(filename).toURI)
    try {
      for (line <- src.getLines()) {
        if (line.startsWith("@")) {
          parseEntry(curString) match {
            case None => ()
            case Some(p) => processEntry(p)
          }
          curString = line.substring(1)
        } else curString += line
      }
      parseEntry(curString) match {
        case None => ()
        case Some(p) => processEntry(p)
      }
    } catch { case ex: Exception => logger.error("File I/O exception", ex) }
    finally { src.close() }
  }

  type LogConfig = (Int, String)
  private val defaultConf = (0, "")

  def measureRecordQE(lb: LogConfig = defaultConf): BuiltInTactic = new BuiltInTactic("logQE") {
    override def result(pr: ProvableSig): ProvableSig = {
      if (pr.subgoals.length == 1) {
        val sequent = pr.subgoals(0)
        if (measure(sequent) > lb._1) logSequent(pr.conclusion, sequent, lb._2)
      }
      pr
    }
  }

  private var logTactic: Option[BelleExpr] = None

  def getLogTactic: BelleExpr = {
    if (logTactic.isEmpty) logTactic = Some(nil)
    logTactic.get
  }

  // This bakes the recorder into the QE tactic, so it will record every single QE call, including internal ones made by
  // e.g. the ODE solver
  def enableLogging(loglevel: LogConfig = defaultConf): Unit = { logTactic = Some(measureRecordQE(loglevel)) }

  def disableLogging(): Unit = { logTactic = Some(nil) }

  /**
   * Exports the entries of `logPath` as separate files in SMT-Lib format to `exportPath`, filtering out duplicate
   * entries if `filterDuplicates` is true (note: keeps all content in memory, avoid for large log files).
   */
  def exportSmtLibFormat(
      logPath: String,
      exportPath: String,
      printPrefix: Formula => String = _ => "",
      printSuffix: Formula => String = _ => "",
      filterDuplicates: Boolean = false,
  ): Unit = {
    val uniqueIndex: scala.collection.mutable.Map[String, Int] = scala.collection.mutable.Map.empty

    def uniqueName(n: String): String = {
      val name = n.replace(" ", "_")
      uniqueIndex.get(name) match {
        case Some(i) =>
          uniqueIndex(name) = i + 1
          name + "_" + i
        case None =>
          uniqueIndex(name) = 0
          name
      }
    }

    val filePath = if (exportPath.contains("${entryname}")) exportPath else exportPath + "${entryname}"

    val exporter = (f: Formula) => printPrefix(f) + DefaultSMTConverter(f) + printSuffix(f)
    val seqs = scala.collection.mutable.Set.empty[Sequent]
    def `export`(e: (String, Sequent)): Unit = {
      if (!filterDuplicates || !seqs.contains(e._2)) {
        print("Exporting " + e._1 + "...")
        try {
          exportSmtLibFormat(e._2.toFormula, filePath.replace("${entryname}", uniqueName(e._1)), exporter)
          println("done")
        } catch { case ex: Throwable => println("failed: " + ex.getMessage) }
      } else if (filterDuplicates) seqs += e._2
    }
    processLog(parseStr2, export, logPath)
  }

  /** Exports the formula `fml` in SMT-Lib format to `exportFile`. */
  def exportSmtLibFormat(fml: Formula, exportFile: String, exporter: Formula => String): Unit = {
    val f = file(exportFile)
    val fw = new FileWriter(f)
    fw.append(exporter(fml))
    fw.close()
  }

  def main(args: Array[String]): Unit = {
    Configuration.setConfiguration(FileConfiguration)
    PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
    val options = parseOptions(Map(), args.toList)
    options.get("convert") match {
      case Some(format) => format match {
          case "smtlib" =>
            val logPath = options
              .getOrElse("logpath", throw new Exception("Missing log file path, use argument -logpath path/to/logfile"))
            val outputPath = options.getOrElse("outputpath", logPath + "${entryname}.smt2")
            exportSmtLibFormat(logPath, outputPath)
          case _ => throw new Exception("Unknown output format " + format + ", use one of [smtlib]")
        }
      case None => throw new Exception("Missing output format, use -convert smtlib")
    }
  }

  @tailrec
  private def parseOptions(parsedOptions: Map[String, String], options: List[String]): Map[String, String] =
    options match {
      case Nil => parsedOptions
      case "-convert" :: value :: tail => parseOptions(parsedOptions ++ Map("convert" -> value), tail)
      case "-logpath" :: value :: tail => parseOptions(parsedOptions ++ Map("logpath" -> value), tail)
      case "-outputpath" :: value :: tail => parseOptions(parsedOptions ++ Map("outputpath" -> value), tail)
      case option :: tail =>
        logger.warn("[Warning] Unknown option " + option + "\n\n"); parseOptions(parsedOptions, tail)
    }

}
