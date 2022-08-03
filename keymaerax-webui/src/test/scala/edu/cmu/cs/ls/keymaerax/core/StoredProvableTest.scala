/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/

package edu.cmu.cs.ls.keymaerax.core

import edu.cmu.cs.ls.keymaerax.{Configuration, FileConfiguration}
import edu.cmu.cs.ls.keymaerax.btactics.RandomFormula
import testHelper.KeYmaeraXTestTags.{SlowTest, SummaryTest, TodoTest, UsualTest}

import scala.collection.immutable._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXPrettyPrinter
import org.scalatest.{FlatSpec, Matchers, PrivateMethodTester}
import edu.cmu.cs.ls.keymaerax.infrastruct.Augmentors.FormulaAugmentor
import org.scalatest.concurrent.{Signaler, TimeLimits}
import org.scalatest.time._

/**
 * Random Provable constructions that are stored, read again, tampered with, read again.
 * @author Andre Platzer
 */
class StoredProvableTest extends FlatSpec with Matchers with PrivateMethodTester with TimeLimits {
  Configuration.setConfiguration(FileConfiguration)
  PrettyPrinter.setPrinter(KeYmaeraXPrettyPrinter.pp)
  val randomTrials = 1000
  val randomComplexity = 20
  val tamperComplexity = 4
  val rand = new RandomFormula()

  "Future-compatible Stored Provable" should "FEATURE_REQUEST: already support block quantifiers" taggedAs TodoTest in {
    val pr = Provable.startProof(Forall(Variable("x")::Variable("y")::Nil, True)) (Skolemize(SuccPos(0)), 0) (CloseTrue(SuccPos(0)), 0)
    pr shouldBe 'proved
    val str = Provable.toStorageString(pr)
    println(str)
    // toStorageString stores block quantifier, but fromStorageString reads nested quantifiers from block quantifier string
    val readagain = Provable.fromStorageString(str)
    readagain shouldBe pr
  }

  "Stored Provable" should "be written and reread correctly (summary)" taggedAs SummaryTest in {test(10,4, 20)}
  it should "be written and reread correctly (usual)" taggedAs UsualTest in {test(100,8, 20)}
  it should "be written and reread correctly (slow)" taggedAs SlowTest in {test(randomTrials,randomComplexity, 60)}

  private def test(randomTrials: Int= randomTrials, randomComplexity: Int = randomComplexity, timeout: Int = 20): Unit =
    cancelAfter(Span(timeout, Minutes)) {
      for (_ <- 1 to randomTrials) {
        if (Thread.currentThread().isInterrupted) cancel()
        val e = rand.nextProvable(randomComplexity).underlyingProvable
        e shouldBe 'proved
        val str = Provable.toStorageString(e)
        val readagain = Provable.fromStorageString(str)
        readagain shouldBe e
      }
    }

  "Tampered Stored Provable" should "be rejected upon rereading (summary)" taggedAs SummaryTest in {testTamper(10,Math.min(4,randomComplexity), 20)}
  it should "be rejected upon rereading (usual)" taggedAs UsualTest in {testTamper(100,Math.min(8,randomComplexity), 20)}
  it should "be rejected upon rereading (slow)" taggedAs SlowTest in {testTamper(randomTrials,randomComplexity, 60)}

  private def testTamper(randomTrials: Int= randomTrials, randomComplexity: Int = randomComplexity, timeout: Int = 20): Unit = {
    implicit val signaler: Signaler = (t: Thread) => {
      t.interrupt()
    }
    cancelAfter(Span(timeout, Minutes)) {
      for (_ <- 1 to randomTrials) {
        if (Thread.currentThread().isInterrupted) cancel()
        val e = rand.nextProvable(randomComplexity).underlyingProvable
        e shouldBe 'proved
        val str = Provable.toStorageString(e)
        val readagain = Provable.fromStorageString(str)
        readagain shouldBe e
        tamperString(str, randomTrials / 10)
      }
    }
  }

  private def tamperString(stored: String, randomTrials: Int= randomTrials, tamperComplexity: Int = tamperComplexity): Unit =
    for (_ <- 1 to randomTrials) {
      if (Thread.currentThread().isInterrupted) cancel()
      val readagain = Provable.fromStorageString(stored)
      val separator = stored.lastIndexOf("::")
      val storedChecksum = stored.substring(separator+2)
      tamperFact(storedChecksum, readagain, randomTrials/10, tamperComplexity)
    }

  private def tamperFact(chksum: String, fact: Provable, randomTrials: Int= randomTrials, tamperComplexity: Int = tamperComplexity): Unit = {
    val toExt = PrivateMethod[String]('toExternalString)
    val pseudotampered = Provable.invokePrivate(toExt(fact.conclusion)) +
      (if (fact.subgoals.length <= 1) "\n\\qed"
      else "\n\\from   " + fact.subgoals.map(s => Provable.invokePrivate(toExt(s))).mkString("\n\\from   ") + "\n\\qed") +
      "::" + chksum
    fact shouldBe Provable.fromStorageString(pseudotampered)

    for (_ <- 1 to randomTrials) {
      if (Thread.currentThread().isInterrupted) cancel()
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
        case _: ProvableStorageException => /* continue */
        case possible: IllegalStateException if possible.getMessage.contains("Higher-order differential symbols are not supported")=> /* continue */
      }
    }
  }

  /** Tamper with a formula by randomly replacing one of its subexpressions */
  private def tamperFormula(f: Formula, tamperComplexity: Int = tamperComplexity): Formula = {
    // rejection sampling
    for (_ <- 1 to 100) try {
      val pos = rand.nextSubPosition(f, FormulaKind)
      FormulaAugmentor(f).sub(pos) match {
        case Some(t: Term)    =>
          //@note avoid higher-order differentials by allowing differentials only when replacing differential terms
          val repl = rand.nextT(rand.nextNames("z", tamperComplexity / 3 + 1), tamperComplexity,
            dots=false, diffs=StaticSemantics.isDifferential(t), funcs=true)
          return FormulaAugmentor(f).replaceAt(pos, repl)
        case Some(fml: Formula) =>
          //@note avoid higher-order differentials by allowing differentials only when replacing differential formulas
          val repl = rand.nextF(rand.nextNames("z", tamperComplexity / 3 + 1), tamperComplexity,
            modals=true, dotTs=false, dotFs=false, diffs=StaticSemantics.isDifferential(fml), funcs=true)
          return FormulaAugmentor(f).replaceAt(pos, repl)
        case Some(_: Program) => return FormulaAugmentor(f).replaceAt(pos, rand.nextProgram(tamperComplexity))
        case None => throw new AssertionError("nextSubPosition should only find defined positions: " + f + " at " + pos + " is " + FormulaAugmentor(f).sub(pos))
      }
    } catch {
      case possible: CoreException if possible.getMessage.contains("No differentials in evolution domain constraints") => /* continue */
      case possible: ClassCastException if possible.getMessage.contains("cannot be cast to edu.cmu.cs.ls.keymaerax.core.Variable") => /* continue */
      case possible: ClassCastException if possible.getMessage.contains("cannot be cast to edu.cmu.cs.ls.keymaerax.core.DifferentialSymbol") => /* continue */
    }
    True
  }
}
