/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{PartialTactic, TacticStatistics}
import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.btactics.Generator.Generator
import edu.cmu.cs.ls.keymaerax.core.{Expression, Formula, Program}
import edu.cmu.cs.ls.keymaerax.hydra.DatabasePopulator
import edu.cmu.cs.ls.keymaerax.launcher.DefaultConfiguration
import edu.cmu.cs.ls.keymaerax.parser.{KeYmaeraXParser, KeYmaeraXProblemParser}
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser.Declaration
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import org.scalatest.AppendedClues

import scala.io.Source
import scala.language.postfixOps

/**
 * Tutorial test cases.
 *
 * @author Stefan Mitsch
 */
@SlowTest
class TutorialRegressionTester(val tutorialName: String, val url: String) extends TacticTestBase with AppendedClues {

  private val tutorialEntries = {
    println("Reading " + url)
    if (url.endsWith(".json")) DatabasePopulator.readTutorialEntries(url)
    else if (url.endsWith(".kya") || url.endsWith(".kyx")) DatabasePopulator.readKya(url)
    else throw new IllegalArgumentException(s"URL must end in either .json, .kya, or .kyx, but got $url")
  }

  //@todo do not fail on first failing model/tactic/proof, accumulate errors and print

  tutorialName should "parse all models" in {
    tutorialEntries.foreach(e =>
      try { KeYmaeraXProblemParser(e.model) } catch { case ex: Throwable =>
        fail(s"${e.name} model did not parse", ex) })
  }

  it should "parse all tactics" in {
    tutorialEntries.filter(_.tactic.isDefined).foreach(e =>
      try { BelleParser(e.tactic.get._2) } catch { case ex: Throwable =>
        fail(s"Tactic ${e.tactic.get._1} of model ${e.name} did not parse", ex) })
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
      filterNot(e => e.tactic.isDefined && e.tactic.get._3 &&
        qeFinder.findAllMatchIn(e.tactic.get._2).forall(p => p.group("toolName") == tool)).
      foreach(e => println(s"QE tool mismatch: skipping ${e.name}"))
    tutorialEntries.
      filter(e => e.tactic.isDefined && e.tactic.get._3 &&
        qeFinder.findAllMatchIn(e.tactic.get._2).forall(p => p.group("toolName") == tool)).
      map(e => (e.name, e.model, parseProblem(e.model), e.tactic.get))
       .foreach({case (name, model, (decls, invGen), tactic) =>
          println(s"Proving $name with ${tactic._1}")
          val t = BelleParser.parseWithInvGen(tactic._2, Some(invGen), decls)
          val result = try {
            val start = System.currentTimeMillis()
            val proof = db.proveBy(model, t, name)
            val end = System.currentTimeMillis()
            println("Proof Statistics")
            println(s"Model $name, tactic ${tactic._1}")
            println(s"Duration [ms]: ${end-start}")
            println("Tactic LOC/normalized LOC/steps: " +
              Source.fromString(tactic._2).getLines.size + "/" +
              TacticStatistics.lines(t) + "/" +
              TacticStatistics.size(t))
            println("Proof steps: " + proof.steps)
            proof
          } catch {
            case ex: Throwable => fail(s"Exception while proving $name", ex)
          }
          t match {
            case _: PartialTactic => // nothing to do, tactic deliberately allowed to result in a non-proof
            case _ => result shouldBe 'proved withClue name + "/" + tactic._1
          }
       })
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
