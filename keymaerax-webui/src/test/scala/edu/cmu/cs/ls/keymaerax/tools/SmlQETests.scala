/**
  * Copyright (c) Carnegie Mellon University.
  * See LICENSE.txt for the conditions of this license.
  */
package edu.cmu.cs.ls.keymaerax.tools

import edu.cmu.cs.ls.keymaerax.Configuration
import edu.cmu.cs.ls.keymaerax.btactics.{TacticTestBase, TactixLibrary}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary.QE
import edu.cmu.cs.ls.keymaerax.btactics.helpers.QELogger
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.infrastruct.{ExpressionTraversal, PosInExpr}
import edu.cmu.cs.ls.keymaerax.infrastruct.ExpressionTraversal.ExpressionTraversalFunction
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, KeYmaeraXArchivePrinter, PrettierPrintFormatProvider}
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.tags.ExtremeTest
import edu.cmu.cs.ls.keymaerax.tools.ext.{CounterExampleTool, Mathematica, QETacticTool, SimplificationTool, SmlQENoRoundingPrinter, SmlQEPrinter, SmlQEReal64Printer, SmtLibReader}
import edu.cmu.cs.ls.keymaerax.tools.qe.{DefaultSMTConverter, SMTConverter}

import java.io.{File, FileOutputStream, FileReader, FilenameFilter, PrintWriter, StringWriter}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Paths}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent._
import scala.sys.process._
import org.scalatest.prop.TableDrivenPropertyChecks._
import slogging.{FilterLogger, FilterLoggerFactory, LogLevel, LoggerConfig, NullLogger, PrintLoggerFactory, SLF4JLoggerFactory}
import smtlib.trees.Commands.{Logic, NonStandardLogic, SetInfo, SetLogic}
import smtlib.trees.Terms.{Attribute, SKeyword, SSymbol}

import scala.io.Source
import scala.util.Try

@ExtremeTest
class SmlQETests extends TacticTestBase {
  object BenchmarkResult {
    val csvHeader: String = "Name,Index,Status,Timeout[ms],Duration[ms],Result,Logic,Expected,Input BV, Input FV"
  }
  case class BenchmarkResult(name: String, index: Long, status: String, result: String, timeout: Int, duration: Long,
                             ex: Option[Throwable] = None, info: Map[String, String] = Map.empty) {
    override def toString: String =
      s"""Proof Statistics ($name $status in logic ${info.getOrElse("logic", "<unknown>")} with time budget $timeout)
         |Expected: ${info.getOrElse("status", "<unknown>")}
         |Result: $result
         |Duration [ms]: $duration""".stripMargin

    def toCsv(infoPrinter: Map[String, String]=>String = info=>
      "," + info.getOrElse("logic", "unknown") +
      "," + info.getOrElse("status", "unknown") +
      "," + info.getOrElse("boundvars","unknown") +
      "," + info.getOrElse("freevars","unknown")): String =
      s"""$name,$index,$status,$timeout,$duration,"${result.replaceAllLiterally("\"","\"\"")}"${infoPrinter(info)}"""
  }

  def files(f: Formula, name: String, rounding: Boolean): List[(String, String)] = {
    List(
      "sml" ->
      s"""open VS;
        |val e = ${if (rounding) SmlQEReal64Printer(f) else (SmlQENoRoundingPrinter(f))};
        |val noquantifiers = case CommandLine.arguments () of
        |         []                 => (print ("Expected QE method: one of [qE_dnf_eq,qE_dnf_general]\\n"); NONE)
        |       | ["qE_dnf_eq"]      => SOME (vSEquality e)
        |       | ["qE_dnf_general"] => SOME (vSGeneral e)
        |       | ["qE_G_3_times"]   => SOME(vSGeneral_3_times e)
        |       | ["qE_E_3_times"]   => SOME(vSEquality_3_times e)
        |       | ["vsLucky"]         => SOME(vSLucky e)
        |       | ["vsLEG"]          => SOME(vsleg e)
        |       | args               => (print("Too many arguments, expected only QE method: one of [qE_dnf_eq,qE_dnf_general]\\n"); NONE);
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
        |$$(BENCHMARK_BASE)/${if (rounding) "roundingfloat" + name.stripPrefix("rounding") else ""}.sml""".stripMargin)
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
      val replIdx = logLines.indexOf("Reduce SMT-LIB 2.0 REPL ...")
      if (replIdx+1 >= logLines.length) BenchmarkResult(_, _, "timeout", "", TIMEOUT*1000, _)
      else logLines(replIdx+1) match {
        case r@"unsat" => BenchmarkResult(_, _, "aproved", r, TIMEOUT*1000, _)
        case r@("sat" | "unknown") => BenchmarkResult(_, _, "sat/unknown", r, TIMEOUT*1000, _)
        case e if e.startsWith("+++ Error") => BenchmarkResult(_, _, "error", logLines.mkString, TIMEOUT*1000, _)
        case _ => BenchmarkResult(_, _, "undefined", logLines.mkString, TIMEOUT*1000, _)
      }
    })
  }

  it should "convert SMT-RAT results" in {
    convertResults("smtrat", (logLines: List[String])=>logLines.headOption match {
      case None => BenchmarkResult(_, _, "timeout", "", TIMEOUT*1000, _)
      case Some(r@"unsat") => BenchmarkResult(_, _, "aproved", r, TIMEOUT*1000, _)
      case Some(r@("sat" | "unknown")) => BenchmarkResult(_, _, "sat/unknown", r, TIMEOUT*1000, _)
      case Some(e) if e.startsWith("ERROR") => BenchmarkResult(_, _, "error", logLines.mkString, TIMEOUT*1000, _)
      case Some(_) => BenchmarkResult(_, _, "undefined", logLines.mkString, TIMEOUT*1000, _)
    })
  }

  it should "convert Virtual Substitution results" in {
    convertResults("virtsubst", (logLines: List[String])=>logLines.headOption match {
      case None => BenchmarkResult(_, _, "timeout", "", TIMEOUT*1000, _)
      case Some(r@"true") => BenchmarkResult(_, _, "aproved", r, TIMEOUT*1000, _)
      case Some(r@"false") => BenchmarkResult(_, _, "disproved", r, TIMEOUT*1000, _)
      case Some(_) => BenchmarkResult(_, _, "simplified", logLines.mkString, TIMEOUT*1000, _)
    })
  }

  it should "convert Z3 results" in {
    convertResults("z3", (logLines: List[String])=>logLines.headOption match {
      case None => BenchmarkResult(_, _, "timeout", "", TIMEOUT * 1000, _)
      case Some(r@"unsat") => BenchmarkResult(_, _, "aproved", r, TIMEOUT * 1000, _)
      case Some(r@"sat") => BenchmarkResult(_, _, "sat", r, TIMEOUT * 1000, _)
      case Some(r@"unknown") => BenchmarkResult(_, _, "unknown", r, TIMEOUT * 1000, _)
      case Some(_) => BenchmarkResult(_, _, "error", logLines.mkString, TIMEOUT * 1000, _)
    })
  }

  private def runMathematicaExperiments(tool: Mathematica, ending: String, converter: File=>(List[Expression], Map[String, String])): Unit = {
    //@note set working directory in test case configuration
    val pwd = new File(System.getProperty("user.dir"))
    val categories = pwd.listFiles().filter(_.isDirectory)

    // @note inconvenient way to export Mathematica Notebook content: comment "Running"/"Done" println, uncomment println, and add in MathematicaQETool:
    // println(MathematicaOpSpec(MathematicaOpSpec.symbol("AbsoluteTiming"))(
    //        MathematicaOpSpec.memoryConstrained(MathematicaOpSpec.timeConstrained(input, MathematicaOpSpec.long(30)), MathematicaOpSpec.long(8000L*1000000L)) :: Nil
    //      ).toString + "},1],")

//    println("results = {")
    for (c <- categories) {
//      println("{ \"" + c.getName + "\", {")
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
//        print("Flatten[{\"" + c.getName + "/" + smtFile.getName + "\",")
        println("Running " + smtFile.getName)
        val start = System.nanoTime()
        val out = Try(tool.qe(fml).fact).toEither
        val dur = System.nanoTime() - start
        println("Done running " + smtFile.getName + "(" + dur / 1000000 + "ms)")
        val result = out match {
          case Right(r) =>
            val (message, result) = if (r.isProved) r.conclusion match {
              case Sequent(IndexedSeq(), IndexedSeq(Equiv(_, True))) => ("aproved", True.prettyString)
              case Sequent(IndexedSeq(), IndexedSeq(Equiv(_, False))) => ("disproved", False.prettyString)
              case Sequent(IndexedSeq(), IndexedSeq(Equiv(_, f))) => ("simplified", f.prettyString)
            } else ("error", r.prettyString)
            BenchmarkResult(smtFile.getName, i, message, result, TIMEOUT * 1000, dur / 1000000, info = infos)
          case Left(_: TimeoutException) => BenchmarkResult(smtFile.getName, i, "timeout", "", TIMEOUT * 1000, dur / 1000000, info = infos)
          case Left(ex) => BenchmarkResult(smtFile.getName, i, "error", ex.getMessage, TIMEOUT * 1000, dur / 1000000, info = infos)
        }
        new PrintWriter(new FileOutputStream(summaryName, true)) {
          try {
            write(result.toCsv() + "\r\n")
          } finally {
            close()
          }
        }
      })
//      println("}},")
    }
//    println("}")
  }

  it should "run all SMT examples with Mathematica CAD" in withTemporaryConfig(Map(
    Configuration.Keys.MATHEMATICA_QE_METHOD -> "Resolve"
  )) {
    withMathematica { runMathematicaExperiments(_, "smt2", (f: File) => SmtLibReader.read(new FileReader(f))) }
  }
  it should "run rounding examples with Mathematica CAD" in withTemporaryConfig(Map(
    Configuration.Keys.MATHEMATICA_QE_METHOD -> "Resolve"
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
    Configuration.Keys.MATHEMATICA_QE_OPTIONS ->
      """CAD -> false,
        |Simplex -> false,
        |SimplifyInequalities -> false,
        |FGLMElimination -> false,
        |LWPreprocessor -> false,
        |QVSPreprocessor -> false,
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
      process.destroy
    }
  }
}
