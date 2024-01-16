/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/**
  * Test Kaisar pass for making controllers total with fallbacks
  * @author Brandon Bohrer
  */
package edu.cmu.cs.ls.keymaerax.cdgl.kaisar

import edu.cmu.cs.ls.keymaerax.btactics.TacticTestBase
import edu.cmu.cs.ls.keymaerax.core.{PrettyPrinter => _, _}
import org.scalactic.Equality
import org.scalatest.Matchers

case class TotalizerTestCase(name: String, model: Statement, sandbox: Statement, fallback: Option[Statement] = None) {
  def prettyString: String =
    s"$name expected sandbox:\n$sandbox\n but got:\n$model"
}

object TotalizerTest {
  def apply(name: String, proof: String, sandbox: String, fallback: Option[String] = None): TotalizerTestCase = {
    val pf =
      try {
        KaisarProgramParser.parseSingle(proof)
      } catch {
        case th: Throwable => throw new Exception("Parse error in test model: " + name, th)
      }
    val sb =
      try {
        KaisarProgramParser.parseSingle(sandbox)
      } catch {
        case th: Throwable => throw new Exception("Parse error in test sandbox: " + name, th)
      }
    val fb = fallback.map(fall => {
      try {
        KaisarProgramParser.parseSingle(fall)
      } catch {
        case th: Throwable => throw new Exception("Parse error in test fallback: " + name, th)
      }})
    TotalizerTestCase(name, pf, sb, fb)
  }
}

class TotalizerTests extends TacticTestBase with Matchers {
  val pldiStreamlined: TotalizerTestCase = TotalizerTest("Streamlined PLDI model", SharedModels.pldiStreamlined, SharedModels.pldiStreamlinedSandbox)
  val allTests: List[TotalizerTestCase] = List(pldiStreamlined)

  "Totality pass" should "make PLDI model total" in withMathematica { _ =>
    allTests.foreach (ttc => {
      Totalizer.useComments = false
      val result = Totalizer(ttc.model, ttc.fallback)
      println("Result:\n" + PrettyPrinter.full(result))
      // Fancy equality
      implicit val equiv: Equality[Statement] = ProofEquality
      (result should equal (ttc.sandbox)) withClue s"in testcase ${ttc.prettyString}"
    })
  }
}
