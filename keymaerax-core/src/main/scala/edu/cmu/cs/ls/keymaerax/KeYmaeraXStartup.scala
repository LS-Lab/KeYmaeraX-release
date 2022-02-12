package edu.cmu.cs.ls.keymaerax

import edu.cmu.cs.ls.keymaerax.bellerophon.ExhaustiveSequentialInterpreter
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.tools.KeYmaeraXTool

/**
  * Startup support functionality.
  */
object KeYmaeraXStartup {

  /** Initializes and updates the lemma cache. */
  def initLemmaCache(logger: (String, Throwable) => Unit =  (msg: String, ex: Throwable) => {
    ex.printStackTrace()
    println(msg)
  }): Unit = {
    try {
      //Delete the lemma database if KeYmaera X has been updated since the last time the database was populated.
      val cacheVersion = LemmaDBFactory.lemmaDB.version()
      if (Version(cacheVersion) < Version(edu.cmu.cs.ls.keymaerax.core.VERSION))
        LemmaDBFactory.lemmaDB.deleteDatabase()
      KeYmaeraXTool.init(Map(
        KeYmaeraXTool.INIT_DERIVATION_INFO_REGISTRY -> "true",
        KeYmaeraXTool.INTERPRETER -> ExhaustiveSequentialInterpreter.getClass.getSimpleName
      ))
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
