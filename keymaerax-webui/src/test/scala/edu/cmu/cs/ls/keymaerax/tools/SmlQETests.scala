/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.btactics.helpers.QELogger
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, KeYmaeraXArchivePrinter, PrettierPrintFormatProvider}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.ExtremeTest
import edu.cmu.cs.ls.keymaerax.tools.ext.{CounterExampleTool, Mathematica, SimplificationTool, SmlQENoRoundingPrinter, SmlQEReal64Printer, SmtLibReader}
import edu.cmu.cs.ls.keymaerax.tools.qe.{DefaultSMTConverter, SMTConverter}

import java.io.{File, FileOutputStream, FileReader, FilenameFilter, PrintWriter, StringWriter}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent._
import scala.sys.process._
import org.scalatest.prop.TableDrivenPropertyChecks._
import org.slf4j.{LoggerFactory, MarkerFactory}
import smtlib.trees.Commands.SetInfo
import smtlib.trees.Terms.{Attribute, SKeyword, SSymbol}

import scala.collection.mutable.ListBuffer
import scala.io.Source
import scala.util.Try

@ExtremeTest
class SmlQETests extends TacticTestBase {
  object BenchmarkResult {
    val csvHeader: String = "Name,Index,Status,Timeout[ms],Duration[ms],Result,Logic,Expected,Input BV, Input FV"
  }
  abstract class BenchmarkResult {
    def toCsv(infoPrinter: Map[String, String]=>String = defaultInfoPrinter): String
    def defaultInfoPrinter: Map[String, String]=>String = info =>
      "," + info.getOrElse("logic", "unknown") +
      "," + info.getOrElse("status", "unknown") +
      "," + info.getOrElse("boundvars","unknown") +
      "," + info.getOrElse("freevars","unknown")
  }
  case class BenchmarkResultEntry(name: String, index: Long, status: String, result: String, timeout: Int,
                                  duration: Long, ex: Option[Throwable] = None, info: Map[String, String] = Map.empty)
    extends BenchmarkResult {

    override def toString: String =
      s"""Proof Statistics ($name $status in logic ${info.getOrElse("logic", "<unknown>")} with time budget $timeout)
         |Expected: ${info.getOrElse("status", "<unknown>")}
         |Result: $result
         |Duration [ms]: $duration""".stripMargin

    override def toCsv(infoPrinter: Map[String, String]=>String = defaultInfoPrinter): String =
      s"""$name,$index,$status,$timeout,$duration,"${result.replaceAllLiterally("\"","\"\"")}"${infoPrinter(info)}"""
  }
  case class BenchmarkResultList(file: String, fileIdx: Long, overallDuration: Long,
                                 results: List[BenchmarkResultEntry]) extends BenchmarkResult {
    override def toString: String = results.mkString("\r\n")
    override def toCsv(infoPrinter: Map[String, String]=>String = defaultInfoPrinter): String =
      results.map(_.toCsv(infoPrinter)).mkString("\r\n")
  }

  def files(f: Formula, name: String, rounding: Boolean): List[(String, String)] = {
    List(
      "sml" ->
      s"""open VS;
        |val e = ${if (rounding) SmlQEReal64Printer(f) else (SmlQENoRoundingPrinter(f))};
        |val noquantifiers = case CommandLine.arguments () of
        |         []                 => (print ("Expected QE method: one of [qE_dnf_eq,qE_dnf_general]\\n"); NONE)
        |       | ["vsEquality"]     => SOME (vSEquality e)
        |       | ["vsGeneral"]      => SOME (vSGeneral e)
        |       | ["vsGeneral3"]     => SOME(vSGeneral_3_times e)
        |       | ["vsEquality3"]    => SOME(vSEquality_3_times e)
        |       | ["vsLucky"]        => SOME(vSLucky e)
        |       | ["vsLuckiest"]     => SOME(vSLuckiest e)
        |       | ["vsLEG"]          => SOME(vsleg e)
        |       | ["vsHeuristic"]    => SOME(vSHeuristic e)
        |       | ["vsBrowns"]       => SOME(vSBrowns e)
        |       | ["vsLuckyBlocksLimited"]    => SOME(vSLuckyBlocksLimited e)
        |       | ["vsGeneralBlocksLimited"]  => SOME(vSGeneralBlocksLimited e)
        |       | ["vsEqualityBlocksLimited"] => SOME(vSEqualityBlocksLimited e)
        |       | ["vsEqualityBlocks"] => SOME(vSEqualityBlocks e)
        |       | ["vsGeneralBlocks"]  => SOME(vSGeneralBlocks e)
        |       | ["vsLuckyBlocks"]    => SOME(vSLuckyBlocks e)
        |       | ["vsLuckiestBlocks"] => SOME(vSLuckiestBlocks e)
        |       | ["vsLEGBlocks"]      => SOME(vSLEGBlocks e)
        |       | ["vsLuckiestRepeat"] => SOME(vSLuckiestRepeat e)
        |       | args                 => (print("Too many arguments, expected only QE method: one of [qE_dnf_eq,qE_dnf_general,qE_G_3_times,qE_E_3_times,vsLucky,vsLEG,vsHeuristic]\\n"); NONE);
        |case noquantifiers of
        |         SOME result => print (concat [print_fm result, "\\n"])
        |       | NONE => print("\\n");
        |val _ = OS.Process.exit(OS.Process.success);""".stripMargin,
      "mlb" ->
      s"""(* $name.mlb *)
        |$$(SML_LIB)/basis/basis.mlb
        |$$(SML_LIB)/smlnj-lib/Util/smlnj-lib.mlb
        |$$(VIRTSUBST_LIB)/VS${if (rounding) "" else "NoRounding"}.sml
        |$$(VIRTSUBST_LIB)/SyntacticSugar.sml
        |$$(VIRTSUBST_LIB)/Util${if (rounding) "" else "NoRounding"}.sml
        |$$(BENCHMARK_BASE)/${if (rounding) "roundingfloat" + name.stripPrefix("rounding") else name.stripPrefix("examples/") }.sml""".stripMargin)
  }

  private val TIMEOUT = 30

  private def listFiles(dir: File, ending: String): List[File] = {
    dir.listFiles().filter(_.isDirectory).flatMap(listFiles(_, ending)).toList ++ dir.listFiles(new FilenameFilter() {
      override def accept(dir: File, name: String): Boolean = name.endsWith(ending)
    }).filter(_.isFile).toList
  }

  "SmlQEPrinter" should "print simple examples" in {
    SmlQEReal64Printer("x>=0".asFormula) shouldBe "Neg(Atom(Less(Var 0)))"
    SmlQEReal64Printer("\\exists x x=0".asFormula) shouldBe "ExQ (Atom(Eq(Var 0)))"
    SmlQEReal64Printer("\\exists x x=y".asFormula) shouldBe "ExQ (Atom(Eq(minus (Var 0) (Var 1))))"
    SmlQEReal64Printer("\\forall x \\exists y x<=y".asFormula) shouldBe "AllQ (ExQ (Atom(Leq(minus (Var 1) (Var 0)))))"
  }

  private def atoms(t: Term): List[Term] = t match {
    case Times(l, r) => atoms(l) ++ atoms(r)
    case _ => List(t)
  }

  private def naiveNoDiv[T <: Expression](fml: T, tool: SimplificationTool with CounterExampleTool): T = {
    def denominatorsOf(fml: Formula): List[Term] = {
      val denominators = scala.collection.mutable.ListBuffer.empty[Term]
      ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
        override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = e match {
          case Divide(_, _: Number) => Left(None)
          case Divide(_, d) => denominators += d; Left(None)
          case _ => Left(None)
        }
      }, fml)
      denominators.flatMap(atoms).distinct.toList
    }
    ExpressionTraversal.traverseExpr(new ExpressionTraversalFunction() {
      override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = e match {
        case c: ComparisonFormula => denominatorsOf(c).reduceOption(Times) match {
          case Some(d) =>
            val nodiv = c.reapply(
              tool.simplify(Times(c.left, d), Nil),
              tool.simplify(Times(c.right, d), Nil))
            Right(noExp(nodiv))
          case _ => Left(None)
        }
        case _ => Left(None)
      }
    }, fml) match {
      case Some(fml) => fml
    }
  }

  private def noExp[T <: Expression](expr: T): T = {
    ExpressionTraversal.traverseExpr(new ExpressionTraversalFunction() {
      override def preT(p: PosInExpr, e: Term): Either[Option[ExpressionTraversal.StopTraversal], Term] = e match {
        case Power(x, Number(n)) if n.isValidInt && n>=0 =>
          Right(List.fill(n.toIntExact)(x).reduceLeftOption(Times).getOrElse(Number(1)))
        case Power(x, Number(n)) if n.isValidInt && n<0 =>
          Right(Divide(Number(1), noExp(Power(x, Number(-n)))))
        case _ => Left(None)
      }
    }, expr).get
  }

  private def closed(fml: Formula): Formula = StaticSemantics.freeVars(fml).toSet.toList.foldRight(fml)({ case (v, f) => Forall(v::Nil, f) })

  it should "eliminate divisions/exponentials and create sentences" in withMathematica { tool =>
    //@note set working directory in test case configuration
    val pwd = new File(System.getProperty("user.dir"))
    val outDir = new File(pwd, "converted")
    outDir.mkdirs()
    val smtFiles = listFiles(pwd, "smt2").sortBy(_.getName)
    println("Converting " + smtFiles.size + " files")
    Table("filehandle", smtFiles.zipWithIndex:_*).forEvery({ case (file, i) =>
      println("Converting file " + i + ": " + file.getName)
      val (exprs, info) = SmtLibReader.read(new FileReader(file))
      exprs.filter(_.isInstanceOf[Formula]).map(_.asInstanceOf[Formula]) match {
        case Not(fml) :: Nil =>
          val printedInfos = new StringWriter
          info.flatMap({
            case ("logic", v) => None
            // SMT-RAT does not parse NRA
//              v.stripPrefix("QF_") match {
//              case s@"NRA" => SetLogic(NonStandardLogic(SSymbol(s)))
//              case _ => SetLogic(Logic.standardLogicFromString(v.stripPrefix("QF_")))
//            }
            case (k, v) => Some(SetInfo(Attribute(SKeyword(k), Some(SSymbol(v)))))
          }).foreach(smtlib.printer.TailPrinter.printCommand(_, printedInfos))
          //val converted = closed(naiveNoDiv(noExp(fml), tool))
          val converted = closed(noExp(fml))
          val content = DefaultSMTConverter(converted).replaceAllLiterally("_v_", "")
          val fn = new File(outDir, pwd.toURI.relativize(file.toURI).getPath)
          fn.getParentFile.mkdirs()
          Files.write(Paths.get(fn.toURI), (printedInfos + content).getBytes(StandardCharsets.UTF_8))
        case _ :: Nil => fail("Skipping" + file.getName + " because Not(fml) expected")
        case fmls => fail("Skipping" + file.getName + " because " + fmls.size + " entries (expected 1)")
      }
      println("Done converting file " + i + ": " + file.getName)
    })
  }

  private def negate(fml: Formula): Formula = {
    ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
      override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = e match {
        case Forall(v, p) => Right(Exists(v, negate(p)))
        case Exists(v, p) => Right(Forall(v, negate(p)))
        case _ => Right(Not(fml))
      }
    }, fml).getOrElse(fml)
  }

  it should "create negated examples" in {
    //@note set working directory in test case configuration
    val pwd = new File(System.getProperty("user.dir"))
    val outDir = new File(pwd, "negated")
    outDir.mkdirs()
    val smtFiles = listFiles(pwd, "smt2").sortBy(_.getName)
    println("Converting " + smtFiles.size + " files")
    Table("filehandle", smtFiles.zipWithIndex: _*).forEvery({ case (file, i) =>
      println("Converting file " + i + ": " + file.getName)
      val (exprs, info) = SmtLibReader.read(new FileReader(file))
      exprs.filter(_.isInstanceOf[Formula]).map(_.asInstanceOf[Formula]) match {
        case Not(fml) :: Nil =>
          val converted = negate(fml)
          val content = DefaultSMTConverter(converted).replaceAllLiterally("_v_", "")
          val fn = new File(outDir, pwd.toURI.relativize(file.toURI).getPath)
          fn.getParentFile.mkdirs()
          Files.write(Paths.get(fn.toURI), content.getBytes(StandardCharsets.UTF_8))
        case _ :: Nil => fail("Skipping" + file.getName + " because Not(fml) expected")
        case fmls => fail("Skipping" + file.getName + " because " + fmls.size + " entries (expected 1)")
      }
    })
  }

  it should "create SMT-RAT QE examples" in {
    //@note set working directory in test case configuration
    val pwd = new File(System.getProperty("user.dir"))
    val outDir = new File(pwd, "smtrat")
    outDir.mkdirs()
    val smtFiles = listFiles(pwd, "smt2").sortBy(_.getName)
    println("Converting " + smtFiles.size + " files")
    Table("filehandle", smtFiles.zipWithIndex: _*).forEvery({ case (file, i) =>
      println("Converting file " + i + ": " + file.getName)
      val (exprs, _) = SmtLibReader.read(new FileReader(file))
      exprs.filter(_.isInstanceOf[Formula]).map(_.asInstanceOf[Formula]) match {
        case Not(fml) :: Nil =>
          var nextBlock: Option[Quantified] = None
          val quantifiers = ListBuffer.empty[Quantified]
          ExpressionTraversal.traverse(new ExpressionTraversalFunction() {
            override def preF(p: PosInExpr, e: Formula): Either[Option[ExpressionTraversal.StopTraversal], Formula] = e match {
              case Exists(x, p) =>
                nextBlock match {
                  case None => nextBlock = Some(Exists(x, False))
                  case Some(Exists(xs, q)) => nextBlock = Some(Exists(xs ++ x, q))
                }
                p match {
                  case _: Exists => // nothing to do, keep appending
                  case _ =>
                    quantifiers += nextBlock.get
                    nextBlock = None
                }
                Left(None)
              case Forall(x, p) =>
                nextBlock match {
                  case None => nextBlock = Some(Forall(x, False))
                  case Some(Forall(xs, q)) => nextBlock = Some(Forall(xs ++ x, q))
                }
                p match {
                  case _: Forall => // nothing to do, keep appending
                  case _ =>
                    quantifiers += nextBlock.get
                    nextBlock = None
                }
                Left(None)
              case _ => Left(None)
            }
          }, fml)

          val content = DefaultSMTConverter.generateSMT(fml) match {
            case (varDec, fmlContent) =>
              varDec + "(assert " + fmlContent + ")\n" +
              //@todo try no block quantifiers (eliminate one-by-one) and different orderings
              "(eliminate-quantifiers " + quantifiers.map({
                case Exists(x, _) => "exists " + x.map(_.prettyString).mkString(" ")
                case Forall(x, _) => "forall " + x.map(_.prettyString).mkString(" ")
              }).map("(" + _ + ")").mkString(" ") + ")"
          }
          val fn = new File(outDir, pwd.toURI.relativize(file.toURI).getPath)
          fn.getParentFile.mkdirs()
          Files.write(Paths.get(fn.toURI), content.replaceAllLiterally("_v_", "").getBytes(StandardCharsets.UTF_8))
        case _ :: Nil => fail("Skipping" + file.getName + " because Not(fml) expected")
        case fmls => fail("Skipping" + file.getName + " because " + fmls.size + " entries (expected 1)")
      }
    })
  }

  it should "export KeYmaera X derived axioms examples to SMT-Lib" in {
    //@note set working directory in test case configuration
    val pwd = new File(System.getProperty("user.dir"))
    val log = new File(pwd, "haveqe.txt")
    val outDir = new File(new File(pwd, "smt"), "${entryname}.smt2")
    QELogger.exportSmtLibFormat(log.getAbsolutePath, outDir.getAbsolutePath,
      printPrefix = (_: Formula) =>
        """(set-info :source | KeYmaera X 4.9.3 derived axiom |)
          |(set-info :status unsat)
          |""".stripMargin,
      filterDuplicates = true)
  }

  it should "export Harrison examples to SMT-Lib" in withMathematica { tool =>
    //@note set working directory in test case configuration
    val pwd = new File(System.getProperty("user.dir"))
    val entries = ArchiveParser(Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/benchmarks/qe/harrison.kyx")).mkString)
    Table("entry", entries:_*).forEvery(entry => {
      val smt = DefaultSMTConverter(closed(naiveNoDiv(noExp(entry.model), tool).asInstanceOf[Formula]))
      val name = entry.name.substring(entry.name.lastIndexOf('/')+1).replaceAllLiterally("(","").replaceAllLiterally(")","").replaceAllLiterally(" ", "-")
      Files.write(Paths.get(new File(pwd, name + ".smt2").toURI), smt.getBytes(StandardCharsets.UTF_8))
    })
  }

  it should "export rounding examples to SMT-Lib" in withMathematica { tool =>
    //@note set working directory in test case configuration
    val pwd = new File(System.getProperty("user.dir"))
    val entries = ArchiveParser(Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/benchmarks/qe/rounding.kyx")).mkString)
    Table("entry", entries:_*).forEvery(entry => {
      // otherwise our exporter disallows numbers that cannot be represented as Double, but we want to test whether the tools disallow them when in their input
      val plainNumberConverter = new SMTConverter() {
        override def convertTerm(t: Term): String = t match {
          case Number(n) => n.bigDecimal.toPlainString
          case _ => super.convertTerm(t)
        }
      }
      val fml = closed(noExp(entry.model).asInstanceOf[Formula])
      //@note we print SML here, because SMTLib does not read decimal numbers correctly and so converting
      // the generated SMT2 format creates wrong SML examples; replace numbers in generated SML code manually
      println(entry.name + "\n" + SmlQENoRoundingPrinter(fml))
      val smt = plainNumberConverter(fml)
      val name = entry.name.substring(entry.name.lastIndexOf('/')+1).replaceAllLiterally("(","").replaceAllLiterally(")","").replaceAllLiterally(" ", "-")
      Files.write(Paths.get(new File(pwd, name + ".smt2").toURI), smt.getBytes(StandardCharsets.UTF_8))
    })
  }

  it should "export Counterexample examples to SMT-Lib" in withMathematica { tool =>
    //@note set working directory in test case configuration
    val pwd = new File(System.getProperty("user.dir"))
    val entries = ArchiveParser(Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/benchmarks/qe/cex.kyx")).mkString)
    Table("entry", entries:_*).forEvery(entry => {
      val smt = DefaultSMTConverter(closed(entry.model.asInstanceOf[Formula]))
      val name = entry.name.substring(entry.name.lastIndexOf('/')+1).replaceAllLiterally("(","").replaceAllLiterally(")","").replaceAllLiterally(" ", "-")
      Files.write(Paths.get(new File(pwd, name + ".smt2").toURI), smt.getBytes(StandardCharsets.UTF_8))
    })
  }

  it should "export all KeYmaera examples" in {
    //@note set working directory in test case configuration
    val pwd = new File(System.getProperty("user.dir"))
    val outDir = new File(pwd, "out")
    outDir.mkdirs()
    val smtFiles = listFiles(pwd, "smt2")
    println("Exporting " + smtFiles.size + " files")
    Table("filehandle", smtFiles:_*).forEvery(file => {
      println("Exporting " + file.getName)
      SmtLibReader.read(new FileReader(file))._1.filter(_.isInstanceOf[Formula]).map(_.asInstanceOf[Formula]) match {
        case Not(fml) :: Nil =>
          val bn = pwd.toURI.relativize(file.toURI).toString.stripSuffix(".smt2")
          val fc = files(closed(fml), pwd.getName + File.separator + bn, rounding=false)
          fc.foreach({ case (suffix, content) =>
            val outFile = new File(outDir, bn + "." + suffix)
            outFile.getParentFile.mkdirs()
            Files.write(Paths.get(outFile.toURI), content.getBytes(StandardCharsets.UTF_8))
          })
          println("Done exporting " + file.getName)
        case _ :: Nil => println("Skipping" + file.getName + " because Not(fml) expected")
        case fmls => println("Skipping" + file.getName + " because " + fmls.size + " entries (expected 1)")
      }
    })
  }

  /** Returns the duration from lines `user` and `sys` in ms. */
  private def parseDuration(logLines: List[String]): Long = {
    def parseDuration(d: String): Long = {
      val minutes :: s :: Nil = d.split("m").toList
      minutes.toLong*60000 + (s.stripSuffix("s").toDouble*1000).toLong
    }
    val user = logLines.find(_.startsWith("user")).map(_.stripPrefix("user").trim).map(parseDuration).getOrElse(0L)
    val sys = logLines.find(_.startsWith("sys")).map(_.stripPrefix("sys").trim).map(parseDuration).getOrElse(0L)
    user + sys
  }

  private def convertResults(tool: String, converter: List[String]=>(String, Long, Long)=>BenchmarkResult): Unit = {
    //@note set working directory in test case configuration
    val pwd = new File(System.getProperty("user.dir"))
    val categories = pwd.listFiles().filter(_.isDirectory)
    for (c <- categories) {
      val summaryName = "summary-" + tool + "-" + c.getName + ".csv"
      val logFiles = listFiles(c, "log").sortBy(_.getName)
      new PrintWriter(summaryName) {
        try {
          write(BenchmarkResult.csvHeader + "\r\n")
        } finally {
          close()
        }
      }
      Table("filehandle", logFiles.zipWithIndex: _*).forEvery({ case (logFile, i) =>
        val log = Source.fromFile(logFile)
        try {
          val logLines = log.getLines().filter(_.nonEmpty).map(_.trim).toList
          val dur = parseDuration(logLines)
          val result = converter(logLines)(logFile.getName.stripSuffix(".log"), i, dur)
          new PrintWriter(new FileOutputStream(summaryName, true)) {
            try {
              write(result.toCsv() + "\r\n")
            } finally {
              close()
            }
          }
        } finally {
          log.close()
        }
      })
    }
  }

  it should "convert Redlog results" in {
    convertResults("redlog", (logLines: List[String])=>{
      val reduceReplIdx = logLines.indexOf("Reduce SMT-LIB 2.0 REPL ...")
      val replIdx =
        if (reduceReplIdx >= 0) reduceReplIdx // up to REDUCE version 5758
        else {
          val i = logLines.indexOf("Redlog SMT-LIB 2 REPL Revision 5825 of 2021-06-13, 19:42:16Z")
          if (i+3 < logLines.length) logLines(i+3) match {
            case "success" => i+3
            case _ => ???
          } else i
        } // REDUCE version 5847
      if (replIdx+1 >= logLines.length) BenchmarkResultEntry(_, _, "timeout", "", TIMEOUT*1000, _)
      else logLines(replIdx+1) match {
        case r@"unsat" => BenchmarkResultEntry(_, _, "aproved", r, TIMEOUT*1000, _)
        case r@("sat" | "unknown") => BenchmarkResultEntry(_, _, "sat/unknown", r, TIMEOUT*1000, _)
        case e if e.startsWith("+++ Error") => BenchmarkResultEntry(_, _, "error", logLines.mkString, TIMEOUT*1000, _)
        case _ => BenchmarkResultEntry(_, _, "undefined", logLines.mkString, TIMEOUT*1000, _)
      }
    })
  }

  it should "convert SMT-RAT results" in {
    convertResults("smtrat", (logLines: List[String])=>logLines.headOption match {
      case None => BenchmarkResultEntry(_, _, "timeout", "", TIMEOUT*1000, _)
      case Some(r@"unsat") => BenchmarkResultEntry(_, _, "aproved", r, TIMEOUT*1000, _)
      case Some(r@("sat" | "unknown")) => BenchmarkResultEntry(_, _, "sat/unknown", r, TIMEOUT*1000, _)
      case Some(e) if e.startsWith("ERROR") => BenchmarkResultEntry(_, _, "error", logLines.mkString, TIMEOUT*1000, _)
      case Some(_) => BenchmarkResultEntry(_, _, "undefined", logLines.mkString, TIMEOUT*1000, _)
    })
  }

  it should "convert SMT-RAT QE results" in {
    convertResults("smtrat", (logLines: List[String])=>logLines.find(_.startsWith("Equivalent Quantifier-Free Formula:")) match {
      case None => BenchmarkResultEntry(_, _, "timeout", "", TIMEOUT*1000, _)
      case Some(r@"Equivalent Quantifier-Free Formula: true") => BenchmarkResultEntry(_, _, "aproved", "TRUE", TIMEOUT*1000, _)
      case Some(r@"Equivalent Quantifier-Free Formula: false") => BenchmarkResultEntry(_, _, "disproved", "FALSE", TIMEOUT*1000, _)
      case Some(_) => BenchmarkResultEntry(_, _, "undefined", logLines.mkString, TIMEOUT*1000, _)
    })
  }

  it should "convert Virtual Substitution results" in {
    convertResults("virtsubst", (logLines: List[String])=>logLines.headOption match {
      case None => BenchmarkResultEntry(_, _, "timeout", "", TIMEOUT*1000, _)
      case Some(r@"true") => BenchmarkResultEntry(_, _, "aproved", r, TIMEOUT*1000, _)
      case Some(r@"false") => BenchmarkResultEntry(_, _, "disproved", r, TIMEOUT*1000, _)
      case Some(_) => BenchmarkResultEntry(_, _, "simplified", logLines.mkString, TIMEOUT*1000, _)
    })
  }

  it should "convert Z3 results" in {
    convertResults("z3", (logLines: List[String])=>logLines.headOption match {
      case None => BenchmarkResultEntry(_, _, "timeout", "", TIMEOUT * 1000, _)
      case Some(r@"unsat") => BenchmarkResultEntry(_, _, "aproved", r, TIMEOUT * 1000, _)
      case Some(r@"sat") => BenchmarkResultEntry(_, _, "sat", r, TIMEOUT * 1000, _)
      case Some(r@"unknown") => BenchmarkResultEntry(_, _, "unknown", r, TIMEOUT * 1000, _)
      case Some(_) => BenchmarkResultEntry(_, _, "error", logLines.mkString, TIMEOUT * 1000, _)
    })
  }

  it should "convert Mathematica results" in {
    //@note converts the results from the Docker container, the Mathematica notebook outputs a CSV directly
    convertResults("mathematica", (logLines: List[String]) => BenchmarkResultList(_, _, _,
      logLines.zipWithIndex.map({ case (l, i) =>
      // format e.g. {cade09converted/ETCS-d-braking-node1346.smt2, {0.090669, {379, True}}}
      val name :: duration :: _ :: result :: Nil =
        l.replaceAllLiterally("{", "").replaceAllLiterally("}", "").split(",").map(_.trim).toList
      result match {
        case "True" => BenchmarkResultEntry(name, i, "aproved", l, TIMEOUT * 1000, (duration.toDouble*1000).toLong)
        case "False" => BenchmarkResultEntry(name, i, "disproved", l, TIMEOUT * 1000, (duration.toDouble*1000).toLong)
        case "$Aborted" => BenchmarkResultEntry(name, i, "timeout", l, TIMEOUT * 1000, (duration.toDouble*1000).toLong)
        case r => BenchmarkResultEntry(name, i, "simplified", r, TIMEOUT * 1000, (duration.toDouble*1000).toLong)
      }
    })))
  }

  private def runMathematicaExperiments(tool: Mathematica, ending: String, converter: File=>(List[Expression], Map[String, String])): Unit = {
    //@note set working directory in test case configuration
    //@note set VM parameter -Dlog4j.configurationFile=log4j-qemathematicaexport.xml
    val pwd = new File(System.getProperty("user.dir"))
    val categories = pwd.listFiles().filter(_.isDirectory)

    LoggerFactory.getLogger(getClass).debug(MarkerFactory.getMarker("mathematica-qe-notebook"),
      "results = {")
    for (c <- categories) {
      LoggerFactory.getLogger(getClass).debug(MarkerFactory.getMarker("mathematica-qe-notebook"),
        "{ \"" + c.getName + "\", {")
      val smtFiles = listFiles(c, ending).sortBy(_.getName)
      tool.setOperationTimeout(TIMEOUT)
      val summaryName = "summary-Mathematica-" + c.getName + ".csv"
      new PrintWriter(summaryName) {
        try {
          write(BenchmarkResult.csvHeader + "\r\n")
        } finally {
          close()
        }
      }
      Table("filehandle", smtFiles.zipWithIndex: _*).forEvery({ case (smtFile, i) =>
        val (Not(fml: Formula) :: Nil, info) = converter(smtFile)
        val infos = info ++ Map(
          "boundvars" -> StaticSemantics.boundVars(fml).toSet.size.toString,
          "freevars" -> StaticSemantics.freeVars(fml).toSet.size.toString
        )
        LoggerFactory.getLogger(getClass).debug(MarkerFactory.getMarker("mathematica-named-qe-cmd"),
          "{\"" + c.getName + "/" + smtFile.getName + "\",AbsoluteTiming[")
        LoggerFactory.getLogger(getClass).debug(MarkerFactory.getMarker("mathematica-qe-notebook"),
          "Flatten[{\"" + c.getName + "/" + smtFile.getName + "\", AbsoluteTiming[")
        println("Running " + smtFile.getName)
        val start = System.nanoTime()
        val out = Try(tool.qe(fml).fact).toEither
        val dur = System.nanoTime() - start
        println("Done running " + smtFile.getName + "(" + dur / 1000000 + "ms)")
        LoggerFactory.getLogger(getClass).debug(MarkerFactory.getMarker("mathematica-named-qe-cmd"), "]}")
        LoggerFactory.getLogger(getClass).debug(MarkerFactory.getMarker("mathematica-qe-notebook"), "]},2],")
        val result = out match {
          case Right(r) =>
            val (message, result) = if (r.isProved) r.conclusion match {
              case Sequent(IndexedSeq(), IndexedSeq(Equiv(_, True))) => ("aproved", True.prettyString)
              case Sequent(IndexedSeq(), IndexedSeq(Equiv(_, False))) => ("disproved", False.prettyString)
              case Sequent(IndexedSeq(), IndexedSeq(Equiv(_, f))) => ("simplified", f.prettyString)
            } else ("error", r.prettyString)
            BenchmarkResultEntry(smtFile.getName, i, message, result, TIMEOUT * 1000, dur / 1000000, info = infos)
          case Left(_: TimeoutException) => BenchmarkResultEntry(smtFile.getName, i, "timeout", "", TIMEOUT * 1000, dur / 1000000, info = infos)
          case Left(ex) => BenchmarkResultEntry(smtFile.getName, i, "error", ex.getMessage, TIMEOUT * 1000, dur / 1000000, info = infos)
        }
        new PrintWriter(new FileOutputStream(summaryName, true)) {
          try {
            write(result.toCsv() + "\r\n")
          } finally {
            close()
          }
        }
      })
      LoggerFactory.getLogger(getClass).debug(MarkerFactory.getMarker("mathematica-qe-notebook"), "}},")
    }
    LoggerFactory.getLogger(getClass).debug(MarkerFactory.getMarker("mathematica-qe-notebook"), "}")
  }

  it should "run all SMT examples with Mathematica CAD" in withTemporaryConfig(Map(
    Configuration.Keys.MATHEMATICA_QE_METHOD -> "Resolve",
    Configuration.Keys.QE_TIMEOUT_INITIAL -> "30",
    Configuration.Keys.QE_TIMEOUT_CEX -> "0",
    Configuration.Keys.QE_TIMEOUT_MAX -> "0"
  )) {
    withMathematica { runMathematicaExperiments(_, "smt2", (f: File) => SmtLibReader.read(new FileReader(f))) }
  }
  it should "run rounding examples with Mathematica CAD" in withTemporaryConfig(Map(
    Configuration.Keys.MATHEMATICA_QE_METHOD -> "Resolve",
    Configuration.Keys.QE_TIMEOUT_INITIAL -> "30",
    Configuration.Keys.QE_TIMEOUT_CEX -> "0",
    Configuration.Keys.QE_TIMEOUT_MAX -> "0"
  )) {
    val pwd = new File(System.getProperty("user.dir"))
    val entries = ArchiveParser(Source.fromInputStream(getClass.getResourceAsStream("/keymaerax-projects/benchmarks/qe/rounding.kyx")).mkString)
    entries.map(e => {
      val outFile = File.createTempFile(e.name, ".kyx", new File(pwd, "rounding"))
      outFile.deleteOnExit()
      val content = new KeYmaeraXArchivePrinter(PrettierPrintFormatProvider(_, 80))(e)
      Files.write(Paths.get(outFile.toURI), content.getBytes(StandardCharsets.UTF_8))
    })

    withMathematica { runMathematicaExperiments(_, "kyx", (f: File) =>
      //@note negate formula consistent with SMTLIB format decision problems
      (ArchiveParser(Source.fromFile(f).mkString).map(e => Not(e.model.asInstanceOf[Formula])), Map.empty)
    ) }
  }
  it should "run all examples with Mathematica VS" in withTemporaryConfig(Map(
    Configuration.Keys.MATHEMATICA_QE_METHOD -> "Resolve",
    Configuration.Keys.QE_TIMEOUT_INITIAL -> "30",
    Configuration.Keys.QE_TIMEOUT_CEX -> "0",
    Configuration.Keys.QE_TIMEOUT_MAX -> "0",
    Configuration.Keys.MATHEMATICA_QE_OPTIONS ->
      """CAD -> false,
        |Simplex -> false,
        |SimplifyInequalities -> false,
        |FGLMElimination -> false,
        |LWPreprocessor -> false,
        |QVSPreprocessor -> false,
        |LinearEquations -> false,
        |LinearOptimizationQE -> false,
        |LinearQE -> true,
        |QuadraticQE -> true""".stripMargin
  )) {
    withMathematica { runMathematicaExperiments(_, "smt2", (f: File) => SmtLibReader.read(new FileReader(f))) }
  }
  it should "run all examples with Mathematica VS+Heu" in withTemporaryConfig(Map(
    Configuration.Keys.MATHEMATICA_QE_METHOD -> "Resolve",
    Configuration.Keys.MATHEMATICA_QE_OPTIONS ->
      """CAD -> false,
        |Simplex -> false,
        |LinearQE -> true,
        |QuadraticQE -> true""".stripMargin
  )) {
    withMathematica { runMathematicaExperiments(_, "smt2", (f: File) => SmtLibReader.read(new FileReader(f))) }
  }

  /** Runs command `cmd` asynchronously in its own process with `timeout` [sec]. Returns the console output of the
    * command on exit value=0, None otherwise. */
  private def runCmd(cmd: String, args: Seq[String], timeout: Long = -1): Either[String,(Int,String)] = {
    var result: String = ""
    val pl = ProcessLogger(result = _)
    val (process, cmdFuture) = synchronized {
      val p = Process(cmd, args).run(pl) //cmd.run(pl) // start asynchronously, log output to logger
      (p, Future(blocking(p.exitValue())))
    }
    try {
      val exitVal =
        if (timeout >= 0) Await.result(cmdFuture, duration.Duration(timeout, "sec"))
        else Await.result(cmdFuture, duration.Duration.Inf)
      if (exitVal == 0) Left(result)
      else Right(exitVal -> result)
    } finally {
      process.destroy()
    }
  }
}
