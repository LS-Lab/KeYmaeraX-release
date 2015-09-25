/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.api

import edu.cmu.cs.ls.keymaerax.core.{Program, Formula}
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser
import edu.cmu.cs.ls.keymaerax.tactics.{TacticLibrary2, ConfigurableGenerate}

/**
 * Dependency injection configuration (production system).
 * @author smitsch
 * Created by smitsch on 12/23/14.
 */
object ComponentConfig {
  lazy val generator = new ConfigurableGenerate[Formula]()
  KeYmaeraXParser.setAnnotationListener((p:Program,inv:Formula) => generator.products += (p->inv))
  lazy val db = DBAbstractionObj.defaultDatabase
  lazy val tacticLibrary = new TacticLibrary2(this)
  lazy val keymaeraInitializer = new KeYmaeraInitializer(this)

}
