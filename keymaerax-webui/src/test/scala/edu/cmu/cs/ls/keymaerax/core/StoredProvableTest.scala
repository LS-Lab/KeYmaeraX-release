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
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import org.scalatest.{FlatSpec, Matchers, PrivateMethodTester, TagAnnotation}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.FormulaAugmentor

import scala.collection.immutable._

/**
 * Random Provable constructions that are stored, read again, tampered with, read again.
 * @author Andre Platzer
 */
class StoredProvableTest extends FlatSpec with Matchers with PrivateMethodTester {
  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  val randomTrials = 100
  val randomComplexity = 12 // 5 // 12
  val tamperComplexity = 2
  val rand = new RandomFormula()

  "Stored Provable" should "be written and reread correctly (summary)" taggedAs(SummaryTest) in {test(10,4)}
  it should "be written and reread correctly (usual)" taggedAs(UsualTest) in {test(100,8)}
  it should "be written and reread correctly (slow)" taggedAs(SlowTest) in {test(randomTrials,randomComplexity)}

  private def test(randomTrials: Int= randomTrials, randomComplexity: Int = randomComplexity) =
    for (i <- 1 to randomTrials) {
      val e = rand.nextProvable(randomComplexity).underlyingProvable
      e shouldBe 'proved
      val str = Provable.toStorageString(e)
      val readagain = Provable.fromStorageString(str)
      readagain shouldBe e
    }

  "Tampered Stored Provable" should "be rejected upon rereading (summary)" taggedAs(SummaryTest) in {testTamper(10,Math.min(4,randomComplexity))}
  it should "be rejected upon rereading (usual)" taggedAs(UsualTest) in {testTamper(100,Math.min(8,randomComplexity))}
  it should "be rejected upon rereading (slow)" taggedAs(SlowTest) in {testTamper(randomTrials,randomComplexity)}

  private def testTamper(randomTrials: Int= randomTrials, randomComplexity: Int = randomComplexity) =
    for (i <- 1 to randomTrials) {
      val e = rand.nextProvable(randomComplexity).underlyingProvable
      e shouldBe 'proved
      val str = Provable.toStorageString(e)
      val readagain = Provable.fromStorageString(str)
      readagain shouldBe e
      tamperString(str, randomTrials/10)
    }

  private def tamperString(stored: String, randomTrials: Int= randomTrials, tamperComplexity: Int = tamperComplexity) =
    for (i <- 1 to randomTrials) {
      val readagain = Provable.fromStorageString(stored)
      val separator = stored.lastIndexOf("::")
      val storedChecksum = stored.substring(separator+2).toInt
      val remainder = stored.substring(0, separator)
      tamperFact(""+storedChecksum, readagain, randomTrials/10, tamperComplexity)
    }

  private def tamperFact(chksum: String, fact: Provable, randomTrials: Int= randomTrials, tamperComplexity: Int = tamperComplexity) = {
    val toExt = PrivateMethod[String]('toExternalString)
    for (i <- 1 to randomTrials) {
      val which = rand.rand.nextInt(1 + fact.subgoals.length)
      val (tampered, pos) = if (which == 0) {
        val pos = rand.nextSeqPos(fact.conclusion)
        (fact.conclusion.updated(pos, tamperFormula(fact.conclusion(pos), tamperComplexity)) +: fact.subgoals, pos)
      } else {
        val pos = rand.nextSeqPos(fact.subgoals(which - 1))
        (fact.conclusion +: fact.subgoals.patch(which - 1, fact.subgoals(which - 1).updated(pos, tamperFormula(fact.subgoals(which - 1)(pos), tamperComplexity)) :: Nil, 1), pos)
      }
      //@see [[Provable.toStorageString]]
      val tamperedStr = Provable.invokePrivate(toExt(tampered.head)) +
        (if (tampered.length <= 1) "\n\\qed"
        else "\n\\from   " + tampered.tail.map(s => Provable.invokePrivate(toExt(s))).mkString("\n\\from   ") + "\n\\qed") +
        "::" + chksum
      try {
        val reread = Provable.fromStorageString(tamperedStr)
        if (reread!=fact) {
          println("TAMPERING SUCCESSFUL at " + which + "(" + pos + ")\n" + fact + "\n" + reread)
          fact shouldBe reread
        }
      } catch {
        case expected: ProvableStorageException => /* continue */
        case possible: IllegalStateException if possible.getMessage.contains("Higher-order differential symbols are not supported")=> /* continue */
      }
    }
  }

  private def tamperFormula(f: Formula, tamperComplexity: Int = tamperComplexity): Formula = {
    //@todo also for other kinds
    val pos = rand.nextSubPosition(f, FormulaKind)
    //@todo swallow and retry CoreException "No differentials in evolution domain constraints"
    FormulaAugmentor(f).replaceAt(pos, rand.nextFormula(tamperComplexity))
  }
}