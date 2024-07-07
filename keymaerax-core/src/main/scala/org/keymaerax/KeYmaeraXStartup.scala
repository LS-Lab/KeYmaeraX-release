/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax

import org.keymaerax.info.Version
import org.keymaerax.lemma.LemmaDBFactory
import org.keymaerax.tools.KeYmaeraXTool

/** Startup support functionality. */
object KeYmaeraXStartup {

  /** Initializes and updates the lemma cache. */
  def initLemmaCache(logger: (String, Throwable) => Unit = (msg: String, ex: Throwable) => {
    ex.printStackTrace()
    println(msg)
  }): Unit = {
    try {
      // Delete the lemma database if KeYmaera X has been updated since the last time the database was populated.
      val cacheVersion = LemmaDBFactory.lemmaDB.version()
      if (cacheVersion < Version) LemmaDBFactory.lemmaDB.deleteDatabase()
      KeYmaeraXTool
        .init(interpreter = KeYmaeraXTool.InterpreterChoice.ExhaustiveSequential, initDerivationInfoRegistry = true)
    } catch {
      case e: Exception =>
        val msg =
          """===> WARNING: Could not prepopulate the derived lemma database. This is a critical error -- KeYmaera X will fail to work! <===
            |You should configure settings in keymaerax.conf and restart KeYmaera X
          """.stripMargin
        logger(msg, e)
        System.err.println(e.getMessage)
        System.err.println(msg)
    }
  }
}
