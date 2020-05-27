package edu.cmu.cs.ls.keymaerax

import edu.cmu.cs.ls.keymaerax.btactics.{DerivationInfoRegistry, Ax}
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.macros.DerivationInfo

/**
  * Startup support functionality.
  */
object KeYmaeraXStartup {

  /** Initializes and updates the lemma cache. */
  def initLemmaCache(logger: (CharSequence, Throwable) => Unit =  (msg: CharSequence, ex: Throwable) => {
    ex.printStackTrace()
    println(msg)
  }): Unit = {
    val allow = Configuration.getOption(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS).getOrElse("false")
    try {
      //Delete the lemma database if KeYmaera X has been updated since the last time the database was populated.
      val cacheVersion = LemmaDBFactory.lemmaDB.version()
      if(StringToVersion(cacheVersion) < StringToVersion(edu.cmu.cs.ls.keymaerax.core.VERSION))
        LemmaDBFactory.lemmaDB.deleteDatabase()
      //Populate the derived axioms database
      Configuration.set(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS, "true", saveToFile = false)
      Ax.prepopulateDerivedLemmaDatabase()
      DerivationInfoRegistry.init
    } catch {
      case e: Exception =>
        val msg =
          """===> WARNING: Could not prepopulate the derived lemma database. This is a critical error -- KeYmaera X will fail to work! <===
            |You should configure settings in keymaerax.conf and restart KeYmaera X
          """.stripMargin
        logger(msg, e)
    } finally {
      Configuration.set(Configuration.Keys.QE_ALLOW_INTERPRETED_FNS, allow, saveToFile = false)
    }
  }
}
