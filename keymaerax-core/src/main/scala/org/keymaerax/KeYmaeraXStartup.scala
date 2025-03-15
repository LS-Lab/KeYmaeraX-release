/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax

import org.keymaerax.info.Version
import org.keymaerax.lemma.LemmaDBFactory
import org.keymaerax.tools.KeYmaeraXTool

/** Startup support functionality. */
object KeYmaeraXStartup extends Logging {

  /** Initializes and updates the lemma cache. */
  def initLemmaCache(): Unit = {
    try {
      // Delete the lemma database if KeYmaera X has been updated since the last time the database was populated.
      val cacheVersion = LemmaDBFactory.lemmaDB.version()
      if (cacheVersion < Version) LemmaDBFactory.lemmaDB.deleteDatabase()
      KeYmaeraXTool
        .init(interpreter = KeYmaeraXTool.InterpreterChoice.ExhaustiveSequential, initDerivationInfoRegistry = true)
    } catch {
      case e: Exception => logger.error(
          """Could not prepopulate the derived lemma database.
            |This is a critical error -- KeYmaera X will fail to work!
            |You should configure settings in keymaerax.conf and restart KeYmaera X
          """.stripMargin,
          e,
        )
    }
  }
}
