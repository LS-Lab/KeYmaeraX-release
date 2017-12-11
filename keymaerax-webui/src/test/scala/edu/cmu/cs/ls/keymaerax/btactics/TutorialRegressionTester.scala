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
import edu.cmu.cs.ls.keymaerax.launcher.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser.Declaration
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import edu.cmu.cs.ls.keymaerax.tools.{SMTQeException, ToolEvidence}
import org.scalatest.AppendedClues

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

  it should "prove all entries flagged as being provable with Mathematica" in withDatabase {
    val provider = new MathematicaToolProvider(DefaultConfiguration.currentMathematicaConfig)
    ToolProvider.setProvider(provider)
    prove("Mathematica")
  }
  it should "prove all entries flagged as being provable with Z3" in withZ3 { _ => withDatabase { prove("Z3") }}

  /** Proves all entries that either use no QE at all, all generic QE, or whose specific QE({`tool`}) (if any) match tool */
  private def prove(tool: String)(db: DbTacticTester) = {
    // finds all specific QE({`tool`}) entries, but ignores the generic QE that works with any tool
    val qeFinder = """QE\(\{`([^`]+)`\}\)""".r("toolName")

    tutorialEntries.
      filterNot(e => e._6.isDefined && e._6.get._3 &&
        qeFinder.findAllMatchIn(e._6.get._2).forall(p => p.group("toolName") == tool)).
      foreach(e => println(s"QE tool mismatch: skipping ${e._1}"))

    forEvery (tutorialEntries.filter(e => e._6.isDefined && e._6.get._3 &&
      qeFinder.findAllMatchIn(e._6.get._2).forall(p => p.group("toolName") == tool))) { (name, model, _, _, _, tactic, kind) =>
      withClue(name + "/" + tactic.get._1) {
        val (decls, invGen) = parseProblem(model)
        println(s"Proving $name with ${tactic.get._1}")
        val t = BelleParser.parseWithInvGen(tactic.get._2, Some(invGen), decls)

        val start = System.currentTimeMillis()
        val proof = db.proveBy(model, t, name)
        val end = System.currentTimeMillis()

        println("Proof Statistics")
        println(s"Model $name, tactic ${tactic.get._1}")
        println(s"Duration [ms]: ${end - start}")
        println("Tactic LOC/normalized LOC/steps: " +
          Source.fromString(tactic.get._2).getLines.size + "/" +
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
          case _ => proof shouldBe 'proved withClue name + "/" + tactic.get._1
        }
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
