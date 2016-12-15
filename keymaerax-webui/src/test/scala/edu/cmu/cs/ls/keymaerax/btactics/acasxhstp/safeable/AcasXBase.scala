/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.btactics.{DebuggingTactics, Idioms, TacticTestBase}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.core.{Formula, Lemma}
import edu.cmu.cs.ls.keymaerax.lemma.{LemmaDB, LemmaDBFactory}
import edu.cmu.cs.ls.keymaerax.pt.ProvableSig
import edu.cmu.cs.ls.keymaerax.tags.SlowTest
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence
import org.scalatest.events.Event
import org.scalatest.{Args, Reporter}

import scala.collection._
import scala.language.postfixOps

/**
 * Base class for AcasX proofs as unit tests.
 * @author Khalil Ghorbal
 * @author Jean-Baptiste Jeannin
 * @author Yanni A. Kouskoulas
 * @author Stefan Mitsch
 * @author Andre Platzer
 */
@SlowTest
class AcasXBase extends TacticTestBase {

  /* Running tests programmatically: where to report test results. */
  private val nilReporter: Reporter = new Reporter() { override def apply(event: Event): Unit = {} }

  /* The lemma database for storing/retrieving lemmas. */
  implicit val lemmaDB: LemmaDB = LemmaDBFactory.lemmaDB
  /* Whether or not to lookup lemmas in `rememberAs` tactic. */
  implicit val lookupRememberedLemmas: Boolean = true

  /* Lemmas */
  def storeLemma(fact: ProvableSig, name: Option[String]): String = {
    val evidence = ToolEvidence(immutable.List("input" -> fact.conclusion.prettyString, "output" -> "true")) :: Nil
    // add lemma into DB, which creates an ID for it. use ID to apply the lemma
    val id = lemmaDB.add(Lemma(fact, evidence, name))
    println(s"Lemma ${name.getOrElse("")} stored as $id")
    id
  }

  /** Proves a lemma by running its test case. */
  def runLemmaTest(name: String, proofCaseName: String): Unit = {
    if (!lemmaDB.contains(name)) {
      println(s"Proving $name...")
      runTest(proofCaseName, Args(nilReporter))
      println("...done")
    }
  }

}
