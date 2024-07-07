/*
 * Copyright (c) Carnegie Mellon University, Karlsruhe Institute of Technology.
 * See LICENSE.txt for the conditions of this license.
 */

package org.keymaerax.btactics

import scala.reflect.runtime.universe

/** A tactic provider. Concrete implementations must be `object`. */
trait TacticProvider {

  /**
   * Returns the tactic provider information to extract @Tactic-annotated methods.
   * @example
   *   {{{
   *   object MyProvider extends TacticProvider {
   *     override def getInfo: (Class[_], universe.Type) = (MyProvider.getClass, universe.typeOf[MyProvider.type])
   *   }
   *   }}}
   */
  def getInfo: (Class[_], universe.Type)
}
