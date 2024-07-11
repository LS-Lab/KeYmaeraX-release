/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax

/**
 * Non-soundness-critical implementation of the lemma mechanism.
 *
 * ===Lemma Mechanism===
 * An implementation of a lemma data base using files [[org.keymaerax.lemma.FileLemmaDB]]. A factory
 * [[org.keymaerax.lemma.LemmaDBFactory]] provides instances of lemma databases.
 *
 * @example
 *   {{{
 *   // prove a lemma
 *   val proved = TactixLibrary.proveBy(
 *      Sequent(IndexedSeq(), IndexedSeq("true | x>5".asFormula)),
 *      orR(1) & close
 *    )
 *   // store a lemma
 *   val lemmaDB = LemmaDBFactory.lemmaDB
 *   val evidence = ToolEvidence(immutable.Map("input" -> proved.toString, "output" -> "true")) :: Nil))
 *   val lemmaID = lemmaDB.add(
 *     Lemma(proved, evidence, Some("Lemma <?> test"))
 *   )
 *   // use a lemma
 *   LookupLemma(lemmaDB, lemmaID)
 *   }}}
 *
 * The lemma database returned by the factory can be configured.
 * @example
 *   {{{
 *   LemmaDBFactory.setLemmaDB(new FileLemmaDB)
 *   val lemmaDB = LemmaDBFactory.lemmaDB
 *   }}}
 *
 * @author
 *   Stefan Mitsch
 */
package object lemma {}
