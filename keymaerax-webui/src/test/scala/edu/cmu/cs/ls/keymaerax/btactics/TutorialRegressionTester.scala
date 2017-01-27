/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.parser.BelleParser
import edu.cmu.cs.ls.keymaerax.hydra.DatabasePopulator
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXProblemParser
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import org.scalatest.AppendedClues

import scala.language.postfixOps

/**
 * Tutorial test cases.
 *
 * @author Stefan Mitsch
 */
@SlowTest
class TutorialRegressionTester(val tutorialName: String, val url: String) extends TacticTestBase with AppendedClues {

  private val tutorialEntries = DatabasePopulator.readTutorialEntries(url)

  //@todo do not fail on first failing model/tactic/proof, accumulate errors and print

  tutorialName should "parse all models" in withMathematica { _ =>
    tutorialEntries.foreach(e =>
      try { KeYmaeraXProblemParser(e.model) } catch { case ex: Throwable =>
        fail(s"${e.name} model did not parse", ex) })
  }

  it should "parse all tactics" in withMathematica { _ =>
    tutorialEntries.filter(_.tactic.isDefined).foreach(e =>
      try { BelleParser(e.tactic.get._1) } catch { case ex: Throwable =>
        fail(s"${e.name} tactic did not parse", ex) })
  }

  it should "prove all provable entries" in withMathematica { _ => withDatabase { db =>
    tutorialEntries.filter(e => e.tactic.isDefined && e.tactic.get._2).foreach(e => {
      println(s"Proving ${e.name}")
      (try {
          db.proveBy(e.model, BelleParser(e.tactic.get._1), e.name)
       } catch {
          case ex: Throwable => fail(s"Exception while proving ${e.name}", ex)
       }) shouldBe 'proved withClue e.name})
  }}

}
