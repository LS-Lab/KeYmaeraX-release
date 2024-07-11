/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

/** @note Code Review 2016-08-16 */
package org.keymaerax.lemma

/**
 * Returns lemma database instances. Prefer using this factory over instantiating lemma databases directly.
 *
 * @example
 *   {{{
 *   val lemmaDB = LemmaDBFactory.lemmaDB
 *   }}}
 *
 * Created by smitsch on 9/1/15.
 * @author
 *   Stefan Mitsch
 */
object LemmaDBFactory {

  /** mutable state for switching out default implementation */
  private[this] var lemmaDBInstance: LemmaDB = new CachedLemmaDB(new FileLemmaDB())

  /** Returns the lemma DB */
  def lemmaDB: LemmaDB = lemmaDBInstance

  /** Sets the lemma DB to be returned by [[lemmaDB]] */
  def setLemmaDB(lemmaDB: LemmaDB): Unit = { lemmaDBInstance = lemmaDB }

}
