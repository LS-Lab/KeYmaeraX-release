/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.btactics.RandomFormula
import testHelper.KeYmaeraXTestTags.{CheckinTest, SlowTest, SummaryTest, UsualTest}

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import org.scalatest.{FlatSpec, Matchers, TagAnnotation}

import scala.collection.immutable.Map

/**
 * Random Provable constructions
 * @author Andre Platzer
 */
class RandomProvableTest extends FlatSpec with Matchers {
  val pp = KeYmaeraXPrettyPrinter
  val randomTrials = 400
  val randomComplexity = 6
  val rand = new RandomFormula()

  "Random Provable" should "be proved and prolongued trivially (summary)" taggedAs(SummaryTest) in {test(10)}
  it should "be proved and prolongued trivially (usual)" taggedAs(UsualTest) in {test(1000,10)}
  it should "be proved and prolongued trivially (slow)" taggedAs(SlowTest) in {test(randomTrials,20)}

  private def test(randomTrials: Int= randomTrials, randomComplexity: Int = randomComplexity) =
    for (i <- 1 to randomTrials) {
      val e = rand.nextProvable(randomComplexity)
      e shouldBe 'proved
      // prolong with conclusion identity is a no-op
      e(Provable.startProof(e.conclusion)) shouldBe e
      // use a fact that isn't proved and then continue above with a sub is a no-op
      Provable.startProof(e.conclusion).sub(0)(Provable.startProof(e.conclusion)) shouldBe Provable.startProof(e.conclusion)
//      val sub = rand.rand.nextInt(e.subgoals.length)
//      e(e.sub(sub), sub) shouldBe e
    }

}
