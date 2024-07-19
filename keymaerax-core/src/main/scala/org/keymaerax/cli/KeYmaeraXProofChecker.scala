/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.cli

import org.keymaerax.bellerophon.IOListeners.PrintProgressListener
import org.keymaerax.bellerophon.parser.BelleParser
import org.keymaerax.bellerophon.{
  BelleExpr,
  BelleInterpreter,
  DependentTactic,
  IOListeners,
  LazySequentialInterpreter,
  TacticStatistics,
}
import org.keymaerax.btactics.{TactixLibrary, ToolProvider}
import org.keymaerax.core.{insist, False, Formula, PrettyPrinter, Sequent, USubst}
import org.keymaerax.infrastruct.Augmentors._
import org.keymaerax.lemma.{Lemma, LemmaDBFactory}
import org.keymaerax.parser.{ArchiveParser, Declaration, KeYmaeraXExtendedLemmaParser, ParsedArchiveEntry, Parser}
import org.keymaerax.pt.{IsabelleConverter, ProvableSig, TermProvable}
import org.keymaerax.tools.ToolEvidence
import org.slf4j.{LoggerFactory, MarkerFactory}

import java.io.PrintWriter
import java.net.URLEncoder
import java.nio.file.attribute.BasicFileAttributes
import java.nio.file.{FileSystems, FileVisitResult, Files, Path, Paths, SimpleFileVisitor}
import scala.collection.immutable
import scala.collection.immutable.{List, Nil}
import scala.collection.mutable.ListBuffer
import scala.concurrent.duration.Duration
import scala.concurrent.{Await, ExecutionContext, Future, TimeoutException}
import scala.reflect.io.File

/** Proof checker command-line interface implementation. */
object KeYmaeraXProofChecker {
  // TODO Convert to Scala 3 enum
  object StatisticsPrinter extends Enumeration {
    val Csv: Value = Value
    val ArchNlnCsv: Value = Value
    val ArchHstpCsv: Value = Value
  }

  /** Proves a single entry */
  def proveEntryWithTactic(
      name: String,
      input: Formula,
      fileContent: String,
      defs: Declaration,
      tacticName: String,
      tactic: BelleExpr,
      timeout: Duration,
      outputFileName: Option[String],
      verbose: Boolean,
      args: Seq[String],
  ): ProofStatistics = {
    val inputSequent = Sequent(immutable.IndexedSeq[Formula](), immutable.IndexedSeq(input))

    // @note open print writer to create empty file (i.e., delete previous evidence if this proof fails).
    val sanitized = outputFileName.map(sanitize)
    sanitized.map(File(_)).foreach(_.parent.createDirectory())
    val pw = sanitized.map(new PrintWriter(_))

    val rcfDurationListener = new IOListeners.StopwatchListener((_, t) =>
      t match {
        case DependentTactic("_rcf") => true
        case _ => false
      }
    )

    val qeDurationListener = new IOListeners.StopwatchListener((_, t) =>
      t match {
        case DependentTactic("_QE") => true
        case _ => false
      }
    )

    val origInterpreter = BelleInterpreter.interpreter
    val listeners =
      if (verbose) qeDurationListener :: rcfDurationListener :: new PrintProgressListener(tactic) :: Nil
      else qeDurationListener :: rcfDurationListener :: Nil
    BelleInterpreter.setInterpreter(LazySequentialInterpreter(origInterpreter.listeners ++ listeners))

    val proofStatistics =
      try {
        qeDurationListener.reset()
        rcfDurationListener.reset()
        val proofStart: Long = System.currentTimeMillis()
        val witness = KeYmaeraXProofChecker(timeout, defs)(tactic)(inputSequent)
        val proofDuration = System.currentTimeMillis() - proofStart
        val qeDuration = qeDurationListener.duration
        val rcfDuration = rcfDurationListener.duration
        val proofSteps = witness.steps
        val tacticSize = TacticStatistics.size(tactic)

        if (witness.isProved) {
          assert(witness.subgoals.isEmpty)
          val expected = inputSequent.exhaustiveSubst(USubst(defs.substs))
          // @note pretty-printing the result of parse ensures that the lemma states what's actually been proved.
          insist(Parser.parser.formulaParser(PrettyPrinter.printer(input)) == input, "parse of print is identity")
          // @note assert(witness.isProved, "Successful proof certificate") already checked in line above
          insist(
            witness.proved == expected,
            "Expected to have proved the original problem and not something else, but proved witness deviates from input",
          )
          // @note check that proved conclusion is what we actually wanted to prove
          insist(
            witness.conclusion == expected,
            "Expected proved conclusion to be original problem, but proved conclusion deviates from input",
          )

          // @note printing original input rather than a pretty-print of proved ensures that @invariant annotations are preserved for reproves.
          val evidence = ToolEvidence(List(
            "tool" -> "KeYmaera X",
            "model" -> fileContent,
            "tactic" -> tactic.prettyString,
            "proof" -> "", // @todo serialize proof
          )) :: Nil

          val lemma = outputFileName match {
            case Some(_) =>
              val lemma = Lemma(witness, evidence, Some("user" + java.io.File.separator + name))
              // @see[[org.keymaerax.core.Lemma]]
              assert(lemma.fact.conclusion.ante.isEmpty && lemma.fact.conclusion.succ.size == 1, "Illegal lemma form")
              assert(
                KeYmaeraXExtendedLemmaParser(lemma.toString) ==
                  (lemma.name, lemma.fact.underlyingProvable, lemma.evidence),
                "reparse of printed lemma is not original lemma",
              )
              Some(lemma)
            case None => None
          }

          lemma match {
            case Some(l) => LemmaDBFactory.lemmaDB.add(l)
            case None => // nothing to do
          }

          pw match {
            case Some(w) =>
              assert(lemma.isDefined, "Lemma undefined even though writer is present")
              w.write(EvidencePrinter.stampHead(args))
              w.write("/* @evidence: parse of print of result of a proof */\n\n")
              w.write(lemma.get.toString)
              w.close()
            case None =>
            // don't save proof as lemma since no outputFileName
          }

          ProofStatistics(
            name,
            tacticName,
            "proved",
            Some(witness),
            timeout,
            proofDuration,
            qeDuration,
            rcfDuration,
            proofSteps,
            tacticSize,
          )
        } else {
          // prove did not work
          assert(!witness.isProved)
          assert(witness.subgoals.nonEmpty)
          deleteOutput(pw, outputFileName)

          if (witness.subgoals.exists(s => s.ante.isEmpty && s.succ.head == False)) {
            ProofStatistics(
              name,
              tacticName,
              "unfinished (cex)",
              Some(witness),
              timeout,
              proofDuration,
              qeDuration,
              rcfDuration,
              proofSteps,
              tacticSize,
            )
          } else {
            ProofStatistics(
              name,
              tacticName,
              "unfinished",
              Some(witness),
              timeout,
              proofDuration,
              qeDuration,
              rcfDuration,
              proofSteps,
              tacticSize,
            )
          }
        }
      } catch {
        case _: TimeoutException =>
          BelleInterpreter.kill()
          deleteOutput(pw, outputFileName)
          // prover shutdown cleanup is done when KeYmaeraX exits
          ProofStatistics(name, tacticName, "timeout", None, timeout, -1, -1, -1, -1, -1)
        case ex: Throwable =>
          BelleInterpreter.kill()
          deleteOutput(pw, outputFileName)
          // prover shutdown cleanup is done when KeYmaeraX exits
          ex.printStackTrace()
          ProofStatistics(name, tacticName, "failed", None, timeout, -1, -1, -1, -1, -1)
      } finally { BelleInterpreter.setInterpreter(origInterpreter) }

    proofStatistics
  }

  /**
   * Proves all entries in the given archive file.
   *
   * @param in
   *   Input archive file(s) (either a specific file or a wildcard, e.g. *.kyx)
   * @param out
   *   Output proof file (defaults to input file with .kyp suffix)
   * @param ptOut
   *   Output proof term s-expression into a file
   * @param conjecture
   *   Conjecture file to replace the model in the input file with (either a specific file or a wildcard, e.g. *.kyx)
   * @param tactic
   *   Either a file containing a tactic, or a parseable tactic. Used to prove the entry/entries in the input or
   *   conjecture file.
   * @param tacticName
   *   Which of the tactics in the input file to use (default: check all, falling back to auto if no tactic is listed).
   *   Only used if no tactic is specified.
   * @param timeout
   *   How long to try proving before giving up.
   * @param verbose
   *   Print verbose proof information.
   * @param statistics
   *   How to print proof statistics.
   * @param args
   *   Command line arguments, included when printing evidence.
   */
  def prove(
      in: String,
      out: Option[String],
      ptOut: Option[String],
      conjecture: Option[String],
      tactic: Option[String],
      tacticName: Option[String],
      timeout: Duration,
      verbose: Boolean,
      statistics: StatisticsPrinter.Value,
      args: Seq[String],
  ): Unit = {
    ProvableSig.PROOF_TERMS_ENABLED = ptOut.isDefined

    val inFiles = findFiles(in)
    val archiveContent = inFiles
      .map(p => p -> ArchiveParser.parseFromFile(p.toFile.getAbsolutePath).filterNot(_.isExercise))
    println("Proving entries from " + archiveContent.size + " files")

    val conjectureFiles = conjecture.map(findFiles).getOrElse(List.empty)
    val conjectureContent = conjectureFiles
      .flatMap(p =>
        ArchiveParser.parseFromFile(p.toFile.getAbsolutePath).filterNot(_.isExercise).map(_ -> p).groupBy(_._1.name)
      )
      .toMap
    val duplicateConjectures = conjectureContent.filter(_._2.size > 1)
    // conjectures must have unique names across files
    assert(
      duplicateConjectures.isEmpty,
      "Duplicate entry names in conjecture files:\n" +
        duplicateConjectures.map(c => c._1 + " in " + c._2.map(_._2).mkString(",")),
    )
    // if exactly one conjecture and one solution: replace regardless of names; otherwise: insist on same entry names and replace by entry name
    val entryNamesDiff = archiveContent.flatMap(_._2.map(_.name)).toSet.diff(conjectureContent.keySet)
    assert(
      conjectureContent.isEmpty ||
        (conjectureContent.map(_._2.size).sum == 1 && archiveContent.map(_._2.size).sum == 1) || entryNamesDiff.isEmpty,
      "Conjectures and archives must agree on names, but got diff " + entryNamesDiff.mkString(","),
    )
    assert(conjectureContent.values.flatMap(_.flatMap(_._1.tactics)).isEmpty, "Conjectures must not list tactics")

    val outputFilePrefix = out.getOrElse(in).stripSuffix(".kyp")
    val outputFileSuffix = ".kyp"

    // @note same archive entry name might be present in several .kyx files
    def disambiguateEntry(outName: String, archiveName: String, entryName: String): String =
      (if (outName.endsWith(archiveName)) outName else outName + "-" + archiveName) + "-" + entryName

    val outputFileNames: Map[Path, Map[ParsedArchiveEntry, String]] =
      if (archiveContent.size == 1 && archiveContent.head._2.size == 1)
        Map(archiveContent.head._1 -> Map(archiveContent.head._2.head -> (outputFilePrefix + outputFileSuffix)))
      else archiveContent
        .map({ case (path, entries) =>
          path ->
            entries
              .map(e =>
                e -> sanitize(disambiguateEntry(outputFilePrefix, path.getFileName.toString, e.name) + outputFileSuffix)
              )
              .toMap
        })
        .toMap

    /** Replaces the conjecture of `entry` with the `conjecture`. */
    def replace(entry: ParsedArchiveEntry, conjecture: ParsedArchiveEntry): ParsedArchiveEntry = {
      conjecture.copy(tactics = entry.tactics)
    }

    val archiveStatistics = archiveContent.flatMap({ case (path: Path, entries) =>
      entries.flatMap(entry =>
        proveEntry(
          path,
          replace(
            entry,
            conjectureContent
              .getOrElse(entry.name, conjectureContent.headOption.map(_._2).getOrElse((entry -> path) :: Nil))
              .head
              ._1,
          ),
          outputFileNames(path)(entry),
          ptOut = ptOut,
          tactic = tactic,
          tacticName = tacticName,
          timeout = timeout,
          verbose = verbose,
          args = args,
        )
      )
    })

    archiveStatistics.foreach(println)

    val printer = statistics match {
      case StatisticsPrinter.Csv => CsvProofStatisticsPrinter
      case StatisticsPrinter.ArchNlnCsv => ArchNLNCsvProofStatisticsPrinter
      case StatisticsPrinter.ArchHstpCsv => ArchHSTPCsvProofStatisticsPrinter
    }

    val csvStatistics = printer.print(archiveStatistics)
    val statisticsLogger = LoggerFactory.getLogger(getClass)
    statisticsLogger.info(MarkerFactory.getMarker("PROOF_STATISTICS"), csvStatistics)

    if (archiveStatistics.exists(_.status == "disproved")) sys.exit(-3)
    if (archiveStatistics.exists(_.status == "failed")) sys.exit(-2)
    if (archiveStatistics.exists(_.status == "unfinished (cex)")) sys.exit(-1)
    if (archiveStatistics.exists(_.status == "unfinished")) sys.exit(-1)
  }

  /** Replaces illegal characters in file names. */
  private def sanitize(filename: String): String = URLEncoder
    .encode(filename, "UTF-8")
    .replace(URLEncoder.encode(File.separator, "UTF-8"), File.separator)

  private def proveEntry(
      path: Path,
      entry: ParsedArchiveEntry,
      outputFileName: String,
      ptOut: Option[String],
      tactic: Option[String],
      tacticName: Option[String],
      timeout: Duration,
      verbose: Boolean,
      args: Seq[String],
  ): List[ProofStatistics] = {
    def savePt(pt: ProvableSig): Unit = {
      (pt, ptOut) match {
        case (ptp: TermProvable, Some(path: String)) =>
          val conv = new IsabelleConverter(ptp.pt)
          val source = conv.sexp
          val writer = new PrintWriter(path)
          writer.write(source)
          writer.close()
        case (_: TermProvable, None) =>
          assert(assertion = false, "Proof term output path specified but proof did not contain proof term")
        case (_, None) => ()
      }
    }

    val tacticString = tactic.map(readTactic(_, entry.defs))

    // @note open print writer to create empty file (i.e., delete previous evidence if this proof fails).
    val proofEvidence = File(sanitize(outputFileName))
    if (proofEvidence.exists) proofEvidence.delete()

    val t = (tacticString, tacticName) match {
      case (Some(tac), None) => ("user", "user", tac) :: Nil
      case (Some(tac), Some(req)) => (entry.tactics.filter(_._1 == req) :+ ("user", "user", tac)).head :: Nil
      case (None, _) =>
        if (tacticName.isDefined) entry.tactics.filter(_._1 == tacticName.get)
        else if (entry.tactics.isEmpty) ("auto", "auto", TactixLibrary.autoClose) :: Nil
        else entry.tactics
    }

    println("Proving " + path + "#" + entry.name + " ...")
    if (t.isEmpty) {
      println("Unknown tactic " + tacticName + ", skipping entry")
      ProofStatistics(
        entry.name,
        tacticName.getOrElse("auto").toString,
        "skipped",
        None,
        timeout,
        -1,
        -1,
        -1,
        -1,
        -1,
      ) :: Nil
    } else {
      t.zipWithIndex
        .map({ case ((tacticName, _, tactic), i) =>
          val proofStat = proveEntryWithTactic(
            entry.name,
            entry.model.asInstanceOf[Formula],
            entry.fileContent,
            entry.defs,
            tacticName,
            tactic,
            timeout,
            if (i == 0) Some(outputFileName) else None,
            verbose = verbose,
            args,
          )

          println("Done " + path + "#" + entry.name + " (" + proofStat.status + ")")

          proofStat.witness match {
            case Some(proof) =>
              if (entry.kind == "lemma") {
                val lemmaName = "user" + File.separator + entry.name
                if (LemmaDBFactory.lemmaDB.contains(lemmaName)) LemmaDBFactory.lemmaDB.remove(lemmaName)
                val evidence = Lemma.requiredEvidence(
                  proof,
                  ToolEvidence(
                    List("tool" -> "KeYmaera X", "model" -> entry.fileContent, "tactic" -> entry.tactics.head._2)
                  ) :: Nil,
                )
                LemmaDBFactory.lemmaDB.add(new Lemma(proof, evidence, Some(lemmaName)))
              }
              savePt(proof)
            case None => // nothing to do
          }
          proofStat
        })
    }
  }

  /**
   * Interprets the tactic argument as a file path and reads that file, if it exists. Otherwise, tries to parse the
   * tactic argument as a tactic.
   */
  private def readTactic(tactic: String, defs: Declaration): BelleExpr = {
    val tacticPath = Paths.get(tactic)
    if (Files.exists(tacticPath)) {
      val source = Files.readString(tacticPath)
      BelleParser(source)
    } else { BelleParser.parseWithInvGen(tactic, None, defs, expandAll = false) }
  }

  /** Finds files matching the pattern in fileName (specific file or using glob wildcards). */
  private def findFiles(fileName: String): List[Path] = {
    // specific file, no wildcard support when referring to a specific entry
    if (new java.io.File(fileName).exists || fileName.contains("#")) Paths.get(fileName).toAbsolutePath :: Nil
    else {
      val path = Paths.get(fileName).toAbsolutePath
      val dir = path.getParent
      val pattern = path.getFileName
      val files: ListBuffer[Path] = new ListBuffer[Path]()
      val finder = new SimpleFileVisitor[Path] {
        private val matcher = FileSystems.getDefault.getPathMatcher("glob:" + pattern)
        override def visitFile(file: Path, attrs: BasicFileAttributes): FileVisitResult = {
          if (matcher.matches(file.getFileName)) files.append(file)
          FileVisitResult.CONTINUE
        }
      }
      Files.walkFileTree(dir, finder)
      files.toList
    }
  }

  /** Deletes the output file and closes the printwriter. */
  private def deleteOutput(pw: Option[PrintWriter], outputFileName: Option[String]): Unit = {
    // @note instantiating PrintWriter above has already emptied the output file
    (pw, outputFileName) match {
      case (Some(w), Some(outName)) =>
        w.close()
        File(outName).delete()
      case _ =>
    }
  }
}

/** Checks proofs (aborting after timeout) and returns the [[ProvableSig]] as a witness. */
case class KeYmaeraXProofChecker(timeout: Duration, defs: Declaration) extends (BelleExpr => Sequent => ProvableSig) {

  /** Checker that uses tactic `t`. */
  override def apply(t: BelleExpr): Sequent => ProvableSig = (s: Sequent) => {
    implicit val ec: ExecutionContext = ExecutionContext.global
    try {
      BelleInterpreter.interpreter.start()
      Await.result(Future { TactixLibrary.proveBy(ProvableSig.startProof(s, defs), t) }, timeout)
    } catch {
      case ex: TimeoutException =>
        BelleInterpreter.interpreter.kill()
        ToolProvider.tools().foreach(_.cancel())
        throw ex
    }
  }
}
