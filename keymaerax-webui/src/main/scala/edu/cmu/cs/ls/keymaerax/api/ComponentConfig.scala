/**
* Copyright (c) Carnegie Mellon University.
* See LICENSE.txt for the conditions of this license.
*/
package edu.cmu.cs.ls.keymaerax.api

import edu.cmu.cs.ls.keymaerax.btactics.ConfigurableGenerate
import edu.cmu.cs.ls.keymaerax.core.{Program, Formula}
import edu.cmu.cs.ls.keymaerax.hydra._
import edu.cmu.cs.ls.keymaerax.parser.KeYmaeraXParser

/**
 * Dependency injection configuration (production system).
 * @author smitsch
 * Created by smitsch on 12/23/14.
 */
object ComponentConfig {
  lazy val generator = new ConfigurableGenerate[Formula]()
  KeYmaeraXParser.setAnnotationListener((p:Program,inv:Formula) => generator.products += (p->inv))
  lazy val db = DBAbstractionObj.defaultDatabase
  lazy val keymaeraInitializer = new KeYmaeraInitializer(this)

}
