/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */

package edu.cmu.cs.ls.keymaerax.btactics.acasxhstp.safeable

import java.io.File

import edu.cmu.cs.ls.keymaerax.bellerophon.BelleExpr
import edu.cmu.cs.ls.keymaerax.btactics.BelleLabels._
import edu.cmu.cs.ls.keymaerax.btactics.{Idioms, TacticTestBase}
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

  /** Wraps fml into a ACAS X problem spec. */
  def createAcasXProblemFile(fml: Formula): String =
    s"""Functions.
       |  R abs(R).
       |  R max(R, R).
       |  R min(R, R).
       |End.
       |
         |ProgramVariables.
       |  /** Variables **/
       |  /* horizontal */
       |  R r.    /* relative distance in ft; xi - xo */
       |          /* x = r */
       |  R rv.   /* relative speed -(vi - vo) */
       |  /* vertical */
       |  R h.    /* relative altitude in ft */
       |          /* if negative: the intruder is lower than the ownship */
       |          /* h := hi - ho */
       |          /* z = h */
       |  R dhd.  /* vertical velocity of ownship */
       |  R dhf.  /* target minimum velocity */
       |  R w.    /* velocity bound 1 = lower, -1 = upper */
       |  R ao.   /* vertical acceleration of ownship */
       |  /** Constants **/
       |  R hp.   /* puck height */
       |  R rp.   /* puck radius */
       |  R a.    /* minimal vertical acceleration. Typically g/4 */
       |
         |  R t.
       |  R ro.
       |  R ho.
       |End.
       |Problem. ${fml.prettyString} End.
       |""".stripMargin

  /* Lemmas */
  def storeLemma(fact: ProvableSig, name: String): String = {
    val evidence = ToolEvidence(immutable.List("input" -> fact.conclusion.prettyString, "output" -> "true")) :: Nil
    // add lemma into DB, which creates an ID for it. use ID to apply the lemma
    val id = lemmaDB.add(Lemma(fact, evidence, Some("user" + File.separator + name)))
    println(s"Lemma $name stored as $id")
    id
  }

  def containsLemma(name: String): Boolean = lemmaDB.contains("user" + File.separator + name)

  def removeLemma(name: String): Unit = lemmaDB.remove("user" + File.separator + name)

  def getLemma(name: String): Lemma = lemmaDB.get("user" + File.separator + name).getOrElse(throw new Exception(s"Proof will be partial. Prove $name first"))

  def insertLemma(lemmaName: String): BelleExpr = {
    val lemma = getLemma(lemmaName)
    // when no hyp in lemma
    cut(lemma.fact.conclusion.succ.head) & Idioms.<(
      (cutShow, cohideR('Rlast) & by(lemma)),
      (cutUse, skip)
    )
  }

  /** Proves a lemma by running its test case. */
  def runLemmaTest(name: String, proofCaseName: String): Unit = {
    if (!containsLemma(name)) {
      println(s"Proving $name...")
      runTest(proofCaseName, Args(nilReporter))
      println("...done")
    }
  }

}
