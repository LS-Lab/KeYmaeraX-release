package edu.cmu.cs.ls.keymaera.api

import edu.cmu.cs.ls.keymaera.core.Formula
import edu.cmu.cs.ls.keymaera.hydra._
import edu.cmu.cs.ls.keymaera.tactics.{TacticLibrary2, ConfigurableGenerate}

/**
 * Dependency injection configuration (production system).
 * @author smitsch
 * Created by smitsch on 12/23/14.
 */
object ComponentConfig {
  lazy val generator = new ConfigurableGenerate[Formula]()
  lazy val db = DBAbstractionObj.defaultDatabase
  lazy val tacticLibrary = new TacticLibrary2(this)
  lazy val keymaeraInitializer = new KeYmaeraInitializer(this)
}
