/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics

import java.io.File
import edu.cmu.cs.ls.keymaerax.bellerophon.IOListeners.PrintProgressListener
import edu.cmu.cs.ls.keymaerax.bellerophon._
import edu.cmu.cs.ls.keymaerax.btactics.Generator.Generator
import edu.cmu.cs.ls.keymaerax.btactics.InvariantGenerator.GenProduct
import edu.cmu.cs.ls.keymaerax.core.{Formula, Program}
import edu.cmu.cs.ls.keymaerax.hydra.{DatabasePopulator, TempDBTools}
import edu.cmu.cs.ls.keymaerax.hydra.DatabasePopulator.TutorialEntry
import edu.cmu.cs.ls.keymaerax.lemma.{Lemma, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.parser.{ArchiveParser, Declaration, Parser}
import edu.cmu.cs.ls.keymaerax.tags.{ExtremeTest, SlowTest}
import edu.cmu.cs.ls.keymaerax.tools.{Tool, ToolEvidence}
import org.scalatest.AppendedClues
import org.scalatest.exceptions.TestFailedException

import scala.io.Source
import scala.language.postfixOps
import org.scalatest.prop.TableDrivenPropertyChecks._

import scala.util.matching.Regex

/**
 * Tutorial and case study test cases.
 * @author
 *   Stefan Mitsch
 */
abstract class RegressionTesterBase(val tutorialName: String, val url: String)
    extends TacticTestBase with AppendedClues {

  private def table(entries: List[TutorialEntry]) = {
    Table(
      ("Tutorial name", "Entry name", "Model", "Description", "Title", "Link", "Tactic", "Kind"),
      entries.map(e => (tutorialName, e.name, e.model, e.description, e.title, e.link, e.tactic, e.kind)): _*
    )
  }

  private def table(tactics: List[(String, String, Boolean)]) = {
    Table(("Tactic name", "Tactic content"), tactics.map(t => (t._1, t._2)): _*)
  }

  private lazy val tutorialEntries = table({
    if (url.endsWith(".json")) DatabasePopulator.readTutorialEntries(url)
    else url.lastIndexOf('#') match {
      case -1 if url.endsWith(".kya") || url.endsWith(".kyx") => DatabasePopulator.readKyx(url)
      case i if url.substring(0, i).endsWith(".kya") || url.substring(0, i).endsWith(".kyx") =>
        DatabasePopulator.readKyx(url)
      case _ => throw new IllegalArgumentException(
          s"URL must be either .json, .kya, or .kyx, with optional #entry identifier, but got $url"
        )
    }
  })

  tutorialName should "parse all models" in withZ3 { _ =>
    forEvery(tutorialEntries) { (tutorialName, name, model, _, _, _, _, _) =>
      withClue(tutorialName + "/" + name) { ArchiveParser.parseProblem(model, parseTactics = false) }
    }
  }

  it should "parse all tactics" in withZ3 { _ =>
    forEvery(tutorialEntries.filter(_._7.nonEmpty)) { (tutorialName, name, model, _, _, _, tactics, _) =>
      val defs = ArchiveParser.parseProblem(model, parseTactics = false).defs
      forEvery(table(tactics)) { (tname, ttext) =>
        withClue(tutorialName + "/" + name + "/" + tname) { ArchiveParser.tacticParser(ttext, defs) }
      }
    }
  }

  it should "prove all entries flagged as being provable with Mathematica" in withMathematica { tool =>
    withDatabase { prove(tool, "Mathematica" :: "Z3" :: Nil) }
  }
  it should "prove all entries flagged as being provable with Z3" in withZ3 { tool =>
    withDatabase {
      tool.setOperationTimeout(30) // avoid getting stuck
      prove(tool, "Z3" :: Nil)
    }
  }

  /* Try to see if any of the Mathematica entries work with Z3. Test "fails" if Z3 can prove an entry. */
  it should "try all Mathematica entries also with Z3" in withZ3 { tool =>
    withDatabase { db =>
      val mathematicaEntries = filterEntriesByTool(_.exists(_.group("toolName") == "Mathematica"), replaceQE = true)

      tool.setOperationTimeout(30) // avoid getting stuck
      forEvery(mathematicaEntries) { (_, name, model, _, _, _, tactic, kind) =>
        whenever(tool.isInitialized) {
          try {
            runEntry(name, model, kind, tactic.head, db)
            fail("Now works with Z3: " + tutorialName + "/" + name + "/" + tactic.head._1)
          } catch {
            case _: BelleThrowable => // test "succeeds" (Z3 still fails), so QE("Mathematica") is still required
            case e: TestFailedException
                if e.getMessage.contains("was not proved") => // master/ODE etc. stopped before proof was done
          }
        }
      }
    }
  }

  /**
   * Proves all entries that either use no QE at all, all generic QE, or whose specific QE("tool") (if any) match any of
   * the tools
   */
  private def prove(tool: Tool, tools: List[String])(db: TempDBTools): Unit = {
    forEvery(filterEntriesByTool(_.forall(m => tools.contains(m.group("toolName"))), replaceQE = false)) {
      (_, name, model, _, _, _, tactic, kind) =>
        whenever(tool.isInitialized) { runEntry(name, model, kind, tactic.head, db) }
    }
  }

  private def runEntry(
      name: String,
      model: String,
      kind: String,
      tactic: (String, String, Boolean),
      db: TempDBTools,
  ) = {
    withClue(tutorialName + ": " + name + "/" + tactic._1) {
      val (decls, _) = parseProblem(model)
      println(s"Proving $name with ${tactic._1}")
      val t = ArchiveParser.tacticParser(tactic._2, decls)

      val start = System.currentTimeMillis()
      val proof = db.proveBy(
        model,
        t,
        l => LazySequentialInterpreter(l :+ new PrintProgressListener(t), throwWithDebugInfo = false),
        name,
      )
      val end = System.currentTimeMillis()

      println(s"Proof Statistics (proved: ${proof.isProved})")
      println(s"$tutorialName, model $name, tactic ${tactic._1}")
      println(s"Duration [ms]: ${end - start}")
      println(
        "Tactic LOC/normalized LOC/steps: " + Source.fromString(tactic._2).getLines().size + "/" +
          TacticStatistics.lines(t) + "/" + TacticStatistics.size(t)
      )
      println("Proof steps: " + proof.steps)

      // store lemma
      val lemmaName = "user" + File.separator + name
      if (LemmaDBFactory.lemmaDB.contains(lemmaName)) LemmaDBFactory.lemmaDB.remove(lemmaName)
      val evidence = Lemma.requiredEvidence(
        proof,
        ToolEvidence(List("tool" -> "KeYmaera X", "model" -> model, "tactic" -> t.prettyString)) :: Nil,
      )
      LemmaDBFactory.lemmaDB.add(new Lemma(proof, evidence, Some(lemmaName)))

      t match {
        case _: PartialTactic => // nothing to do, tactic deliberately allowed to result in a non-proof
        case _ => proof shouldBe Symbol("proved") withClue tutorialName + "/" + name + "/" + tactic._1
      }
    }
  }

  /** Parse a problem file to find declarations and invariant annotations */
  private def parseProblem(model: String): (Declaration, Generator[GenProduct]) = {
    TactixInit.invSupplier = FixedGenerator(Nil)
    val generator = new ConfigurableGenerator[GenProduct]()
    Parser
      .parser
      .setAnnotationListener((p: Program, inv: Formula) =>
        generator.products += (p -> (generator.products.getOrElse(p, Nil) :+ (inv, None)))
      )
    val entry = ArchiveParser.parseProblem(model, parseTactics = false)
    TactixInit.invSupplier = generator
    TactixInit.differentialInvGenerator = InvariantGenerator.cached(InvariantGenerator.differentialInvariantGenerator)
    TactixInit.loopInvGenerator = InvariantGenerator.cached(InvariantGenerator.loopInvariantGenerator)
    Parser
      .parser
      .setAnnotationListener((_: Program, _: Formula) => {}) // @note cleanup for separation between tutorial entries
    (entry.defs, generator)
  }

  /** Restricts the tutorialentries to the ones with tactics matching the filter `toolFilter`. */
  private def filterEntriesByTool(toolFilter: Iterator[Regex.Match] => Boolean, replaceQE: Boolean) = {
    // find all specific QE({`tool`}) and QE("tool") entries, but ignores the generic QE that works with any tool
    val qeOldFinder = """QE\(\{`(?<toolName>[^`]+)`\}\)""".r
    val qeFinder = """(QE|useSolver)\("(?<toolName>[^"]+)"\)""".r

    val skipEntries = tutorialEntries.filter(e =>
      e._7.nonEmpty &&
        !e._7
          .exists(t =>
            t._3 && toolFilter(qeFinder.findAllMatchIn(t._2)) && toolFilter(qeOldFinder.findAllMatchIn(t._2))
          )
    )
    skipEntries.foreach(e => println(s"QE tool mismatch: skipping ${e._2}"))

    val result = tutorialEntries.flatMap(e =>
      e._7
        .filter(t => t._3 && toolFilter(qeFinder.findAllMatchIn(t._2)) && toolFilter(qeOldFinder.findAllMatchIn(t._2)))
        .map(t =>
          (
            e._1,
            e._2,
            e._3,
            e._4,
            e._5,
            e._6,
            if (replaceQE) (t._1, qeOldFinder.replaceAllIn(qeFinder.replaceAllIn(t._2, "QE"), "QE"), t._3) :: Nil
            else t :: Nil,
            e._8,
          )
        )
    )
    Table(tutorialEntries.heading, result: _*)
  }
}

@SlowTest
class TutorialRegressionTester(override val tutorialName: String, override val url: String)
    extends RegressionTesterBase(tutorialName, url)

@ExtremeTest
class CaseStudyRegressionTester(override val tutorialName: String, override val url: String)
    extends RegressionTesterBase(tutorialName, url)
