/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import edu.cmu.cs.ls.keymaerax.btactics.RandomFormula
import testHelper.KeYmaeraXTestTags.{CheckinTest, SlowTest, SummaryTest, UsualTest}

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import org.scalatest.{FlatSpec, Matchers, TagAnnotation}

import scala.collection.immutable.Map

/**
 * Random Provable constructions
 * @author
 *   Andre Platzer
 */
class RandomProvableTest extends FlatSpec with Matchers {
  Configuration.setConfiguration(FileConfiguration)
  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  val randomTrials = 40000
  val randomComplexity = 12
  val rand = new RandomFormula()

  "Random Provable" should "be proved and prolongued trivially (summary)" taggedAs (SummaryTest) in { test(10, 4) }
  it should "be proved and prolongued trivially (usual)" taggedAs (UsualTest) in { test(100, 8) }
  it should "be proved and prolongued trivially (slow)" taggedAs (SlowTest) in { test(randomTrials, randomComplexity) }

  private def test(randomTrials: Int = randomTrials, randomComplexity: Int = randomComplexity) =
    for (i <- 1 to randomTrials) {
      val e = rand.nextProvable(randomComplexity)
      e shouldBe Symbol("proved")
      // prolong with conclusion identity is a no-op
      e(ProvableSig.startPlainProof(e.conclusion)) shouldBe e
      // use a fact that isn't proved and then continue above with a sub is a no-op
      ProvableSig.startPlainProof(e.conclusion).sub(0)(ProvableSig.startPlainProof(e.conclusion)) shouldBe
        ProvableSig.startPlainProof(e.conclusion)
//      val sub = rand.rand.nextInt(e.subgoals.length)
//      e(e.sub(sub), sub) shouldBe e
    }

//  "Dual-free" ignore should "work on random formulas if no dual operators occur" in {
  // @todo use boxTrue instead of DualFree
//    val dual = try {
//      Dual(Test(False))
//      false
//    } catch {
//      case _ => true
//    }
//    if (dual) {
//      for (i <- 1 to randomTrials) {
//        import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.FormulaAugmentor
//        val e = Box(rand.nextProgram(randomComplexity), True)
//        if (e.find(prg=>prg.isInstanceOf[Dual])==None)
//          Provable.startProof(e)(DualFree(SuccPos(0)), 0) shouldBe 'proved
//      }
//    } else {
//      for (i <- 1 to randomTrials) {
//        val e = Box(rand.nextProgram(randomComplexity), True)
//        Provable.startProof(e)(DualFree(SuccPos(0)), 0) shouldBe 'proved
//      }
//    }
//  }
}
