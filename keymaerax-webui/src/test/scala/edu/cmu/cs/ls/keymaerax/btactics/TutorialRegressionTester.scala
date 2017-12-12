/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import java.io.File

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleThrowable, PartialTactic, TacticStatistics}
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.Generator.Generator
import edu.cmu.cs.ls.keymaerax.core.{Expression, Formula, Lemma, Program}
import edu.cmu.cs.ls.keymaerax.hydra.DatabasePopulator
import edu.cmu.cs.ls.keymaerax.hydra.DatabasePopulator.TutorialEntry
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser.Declaration
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence
import org.scalatest.AppendedClues
import org.scalatest.exceptions.TestFailedException

import scala.io.Source
import scala.language.postfixOps
import org.scalatest.prop.TableDrivenPropertyChecks._

/**
 * Tutorial test cases.
 *
 * @author Stefan Mitsch
 */
@SlowTest
class TutorialRegressionTester(val tutorialName: String, val url: String) extends TacticTestBase with AppendedClues {

  private def table(entries: List[TutorialEntry]) = {
    Table(("Name", "Model", "Description", "Title", "Link", "Tactic", "Kind"),
      entries.map(e => (e.name, e.model, e.description, e.title, e.link, e.tactic, e.kind)):_*)
  }

  private val tutorialEntries = table({
    println("Reading " + url)
    if (url.endsWith(".json")) DatabasePopulator.readTutorialEntries(url)
    else if (url.endsWith(".kya") || url.endsWith(".kyx")) DatabasePopulator.readKya(url)
    else throw new IllegalArgumentException(s"URL must end in either .json, .kya, or .kyx, but got $url")
  })

  tutorialName should "parse all models" in {
    forEvery (tutorialEntries) { (name, model, _, _, _, _, _) =>
      withClue(name) { KeYmaeraXProblemParser(model) }
    }
  }

  it should "parse all tactics" in {
    forEvery (tutorialEntries.filter(_._6.isDefined)) { (name, _, _, _, _, tactic, _) =>
      withClue(name + "/" + tactic.get._1) { BelleParser(tactic.get._2) }
    }
  }

  it should "prove all entries flagged as being provable with Mathematica" in withMathematica { _ => withDatabase {
    prove("Mathematica")
  }}
  it should "prove all entries flagged as being provable with Z3" in withZ3 { _ => withDatabase { prove("Z3") }}

  /* Try to see if any of the Mathematica entries work with Z3. Test "fails" if Z3 can prove an entry. */
  it should "try all Mathematica entries also with Z3" in withZ3 { tool => withDatabase { db =>
    val qeFinder = """QE\(\{`([^`]+)`\}\)""".r("toolName")

    val mathematicaEntries = tutorialEntries.filter(e => e._6.isDefined && e._6.get._3 &&
        qeFinder.findAllMatchIn(e._6.get._2).exists(p => p.group("toolName") == "Mathematica"))

    tool.setOperationTimeout(30) // avoid getting stuck
    forEvery (mathematicaEntries) { (name, model, _, _, _, tactic, kind) =>
      val t = (tactic.get._1, qeFinder.replaceAllIn(tactic.get._2, "QE"), tactic.get._3)
      try {
        runEntry(name, model, kind, t, db)
        fail("Now works with Z3: " + tutorialName + "/" + name + "/" + t._1)
      } catch {
        case _: BelleThrowable => // test "succeeds" (Z3 still fails), so QE({`Mathematica`}) is still required
        case e: TestFailedException if e.getMessage.contains("was not proved") => // master/ODE etc. stopped before proof was done
      }
    }
  }}

  /** Proves all entries that either use no QE at all, all generic QE, or whose specific QE({`tool`}) (if any) match tool */
  private def prove(tool: String)(db: DbTacticTester) = {
    // finds all specific QE({`tool`}) entries, but ignores the generic QE that works with any tool
    val qeFinder = """QE\(\{`([^`]+)`\}\)""".r("toolName")

    tutorialEntries.
      filterNot(e => e._6.isDefined && e._6.get._3 &&
        qeFinder.findAllMatchIn(e._6.get._2).forall(p => p.group("toolName") == tool)).
      foreach(e => println(s"QE tool mismatch: skipping ${e._1}"))

    forEvery (tutorialEntries.
      filter(e => e._6.isDefined && e._6.get._3 &&
        qeFinder.findAllMatchIn(e._6.get._2).forall(p => p.group("toolName") == tool))) { (name, model, _, _, _, tactic, kind) =>
      runEntry(name, model, kind, tactic.get, db)
    }
  }

  private def runEntry(name: String, model: String, kind: String, tactic: (String, String, Boolean), db: DbTacticTester) = {
    withClue(tutorialName + ": " + name + "/" + tactic._1) {
      val (decls, invGen) = parseProblem(model)
      println(s"Proving $name with ${tactic._1}")
      val t = BelleParser.parseWithInvGen(tactic._2, Some(invGen), decls)

      val start = System.currentTimeMillis()
      val proof = db.proveBy(model, t, name)
      val end = System.currentTimeMillis()

      println(s"Proof Statistics (proved: ${proof.isProved})")
      println(s"$tutorialName, model $name, tactic ${tactic._1}")
      println(s"Duration [ms]: ${end - start}")
      println("Tactic LOC/normalized LOC/steps: " +
        Source.fromString(tactic._2).getLines.size + "/" +
        TacticStatistics.lines(t) + "/" +
        TacticStatistics.size(t))
      println("Proof steps: " + proof.steps)

      if (kind == "lemma") {
        val lemmaName = "user" + File.separator + name
        if (LemmaDBFactory.lemmaDB.contains(lemmaName)) LemmaDBFactory.lemmaDB.remove(lemmaName)
        val evidence = Lemma.requiredEvidence(proof, ToolEvidence(List(
          "tool" -> "KeYmaera X",
          "model" -> model,
          "tactic" -> t.prettyString
        )) :: Nil)
        LemmaDBFactory.lemmaDB.add(new Lemma(proof, evidence, Some(lemmaName)))
      }

      t match {
        case _: PartialTactic => // nothing to do, tactic deliberately allowed to result in a non-proof
        case _ => proof shouldBe 'proved withClue tutorialName + "/" + name + "/" + tactic._1
      }
    }
  }

  /** Parse a problem file to find declarations and invariant annotations */
  private def parseProblem(model: String): (Declaration, Generator[Expression]) = {
    val generator = new ConfigurableGenerator[Formula]()
    KeYmaeraXParser.setAnnotationListener((p: Program, inv: Formula) => generator.products += (p -> inv))
    val (decls, _) = KeYmaeraXProblemParser.parseProblem(model)
    KeYmaeraXParser.setAnnotationListener((_: Program, _: Formula) => {}) //@note cleanup for separation between tutorial entries
    (decls, generator)
  }

}
